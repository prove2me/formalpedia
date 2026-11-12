-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_Backlinks
-- name    : LawlerCompress_TardyJobs_Backlinks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:39.618158+00:00
-- url     : https://prove2.me/theorems/2e14e9d4-cbf6-428e-8610-641d9132512b
-- title:
--   Completed-table and immutable sparse-pointer interface
-- statement:
--   A pointer witness is a finite canonical path. The null pointer describes zero load and zero weight. Each non-null record stores a job, a machine and an earlier predecessor pointer; job indices strictly increase along the path. Adding job j on machine r adds p_j to that coordinate and w_j to the weight, and its resulting completion must lie in C̄_j.
--
--   $$x'=x+p_je_r,\qquad v'=v+w_j,\qquad x_r+p_j\in\bar C_j.$$
--
--   The completed-memory predicate specifies the literal headers, table base and size, the consecutive allocated record region, and a witness for every allocated record. For every reachable final table entry, the memory contains its specified weight and an associated pointer witness with exactly that load and weight. Unreachable entries have a zero flag. The extraction preservation predicate requires every allocated record cell to remain unchanged.
--
--   The preparation and extraction assertions use this interface in the same memory state; no separately supplied favorable state is permitted.
--
--   **Formalization Note** Record addresses are aligned triples after the reusable buffer. The header records the end address. This relation specifies mathematical contents, without asserting any program's correctness or attaching any resource bound to it.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 8, §3.3, Lemma 3.5 and proof, lines 223–242

import Definitions.Def_LawlerCompress_TardyJobs_Programs

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

def header {m : ℕ} (I : Instance m) : ℕ := 2 + 3 * I.n

def tableBase {m : ℕ} (I : Instance m) : ℕ := header I + 18 + 5 * I.n + 2 * m

def tableSize {m : ℕ} (I : Instance m) : ℕ := (dmax I + 1) ^ m

def recordStart {m : ℕ} (I : Instance m) : ℕ :=
  tableBase I + 3 * tableSize I + 3 * m * tableSize I

def loadIndex {m : ℕ} (I : Instance m) (x : Fin m → ℕ) : ℕ :=
  ∑ r, x r * (dmax I + 1) ^ r.val

/-- A finite pointer derivation: jobs increase along the path, and every added job
finishes at its canonical time. Zero is the null pointer. No correctness or resource
assumption about a program is built into this relation. -/
inductive PointerWitness {m : ℕ} (I : Instance m) (σ : Light.State) :
    ℕ → ℕ → (Fin m → ℕ) → ℕ → Prop
  | nil (bound : ℕ) : PointerWitness I σ 0 bound 0 0
  | cons {ptr prev bound w : ℕ} {x : Fin m → ℕ}
      (j : Fin I.n) (r : Fin m)
      (hindex : j.val < bound)
      (hptr : recordStart I ≤ ptr ∧ (ptr - recordStart I) % 3 = 0)
      (hprev : prev = 0 ∨ recordStart I ≤ prev ∧ prev < ptr)
      (hjob : σ.mem ptr = j.val)
      (hmachine : σ.mem (ptr + 1) = r.val)
      (hlink : σ.mem (ptr + 2) = prev)
      (hpast : PointerWitness I σ prev j.val x w)
      (hcanonical : x r + I.p j ∈ cbar I j) :
      PointerWitness I σ ptr bound
        (Function.update x r (x r + I.p j)) (w + I.w j)

/-- The final table and every associated pointer are specified in the very same
memory passed to extraction. K counts precisely the consecutive sparse records.
Every allocated record is a finite canonical path, including discarded candidates;
null is the initial empty path. The concrete code writes records only at the advancing
end pointer. Extraction's postcondition explicitly preserves their entire region. -/
def BacklinkReady {m : ℕ} (I : Instance m) (S : ℕ) (σ : Light.State) : Prop :=
  ∃ K : ℕ,
    (∀ addr < (encode I).length, σ.mem addr = Light.memOf (encode I) addr) ∧
    σ.mem (header I) = dmax I ∧
    σ.mem (header I + 1) = header I + 16 ∧
    σ.mem (header I + 2) = tableBase I ∧
    σ.mem (header I + 3) = tableSize I ∧
    σ.mem (header I + 4) = recordStart I ∧
    σ.mem (header I + 5) = recordStart I + 3 * K ∧
    recordStart I + 3 * K ≤ S ∧
    (∀ k < K, ∃ bound x w,
      PointerWitness I σ (recordStart I + 3 * k) bound x w) ∧
    (∀ x ∈ loads I,
      let cell := tableBase I + 3 * loadIndex I x
      match algTable I I.n x with
      | ⊥ => σ.mem cell = 0
      | (w : ℕ) => σ.mem cell = 1 ∧ σ.mem (cell + 1) = w ∧
          ∃ ptr : ℕ, σ.mem (cell + 2) = ptr ∧
            (ptr = 0 ∨ recordStart I ≤ ptr ∧ ptr < recordStart I + 3 * K) ∧
            PointerWitness I σ ptr I.n x w)

def RecordsPreserved {m : ℕ} (I : Instance m) (σ₁ σ₂ : Light.State) : Prop :=
  ∀ addr : ℕ, recordStart I ≤ addr → (addr : ℤ) < σ₁.mem (header I + 5) →
    σ₂.mem addr = σ₁.mem addr

end LawlerCompress.TardyJobs


