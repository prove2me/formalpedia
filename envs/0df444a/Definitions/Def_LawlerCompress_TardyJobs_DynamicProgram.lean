-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_DynamicProgram
-- name    : LawlerCompress_TardyJobs_DynamicProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:26.301013+00:00
-- url     : https://prove2.me/theorems/6acf71a1-7093-4ed5-83b3-4e2712a56fd1
-- title:
--   Algorithm 2: deferred-update value recurrence
-- statement:
--   Let L={0,…,d_max}^m be the finite load box. The initial table has f₀(0)=0 and f₀(x)=−∞ at every other vector. For the next input job j set
--
--   $$f_{j+1}(x)=\max\bigl\{f_j(x),\ \max_{r:x_r\in\bar C_j,\ p_j\le x_r}\bigl(f_j(x-p_je_r)+w_j\bigr)\bigr\},\qquad x\in L.$$
--
--   Outside L the value is −∞. All candidates read the previous round, exactly as the deferred Updates list in Algorithm 2. The algorithm value is the maximum of the completed table over L. It is a natural number: the zero vector is reachable in every round, so the finite maximum is never −∞. Immediate structural lemmas establish this fact before the conversion to a natural number.
--
--   This is a value specification independent of the finite machine program.
--
--   **Formalization Note** Round k has processed the first k input positions; job indices themselves start at zero. A table value uses WithBot ℕ, where bottom represents −∞. Empty coordinate maxima are bottom when m=0. For m=1 the sole machine coordinate is enumerated, corresponding to the single empty u tuple in Algorithm 2.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), pp. 6–7, §3.2, Equation (2), Algorithm 2 lines 1–15

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

/-- All vectors in the closed load box, including the unique zero-dimensional vector. -/
def loads {m : ℕ} (I : Instance m) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (dmax I + 1))

/-- Outside the box the value is −∞. Every candidate in round j reads the previous
round, not an already modified entry: this is Algorithm 2's deferred update list.
The guard p_j ≤ x_r is explicit so natural subtraction never truncates. -/
def algTable {m : ℕ} (I : Instance m) : ℕ → (Fin m → ℕ) → WithBot ℕ
  | 0, x => if x = 0 then (0 : ℕ) else ⊥
  | k + 1, x =>
    if x ∈ loads I then
      match (List.finRange I.n)[k]? with
      | none => algTable I k x
      | some j => max (algTable I k x)
          (Finset.univ.sup fun r : Fin m =>
            if I.p j ≤ x r ∧ x r ∈ cbar I j then
              algTable I k (Function.update x r (x r - I.p j)) + (I.w j : WithBot ℕ)
            else ⊥)
    else ⊥

/-- A finite maximum; the bottom branch is explicit and is unreachable at round n,
because the zero vector remains reachable. The structural lemma below records it. -/
def algMaximum {m : ℕ} (I : Instance m) : WithBot ℕ :=
  (loads I).sup (algTable I I.n)

def algValue {m : ℕ} (I : Instance m) : ℕ :=
  match algMaximum I with
  | ⊥ => 0
  | (v : ℕ) => v

lemma zero_mem_loads {m : ℕ} (I : Instance m) : (0 : Fin m → ℕ) ∈ loads I := by
  simp [loads, Fintype.mem_piFinset]

lemma zero_reachable {m : ℕ} (I : Instance m) (k : ℕ) :
    (0 : WithBot ℕ) ≤ algTable I k 0 := by
  induction k with
  | zero => simp [algTable]
  | succ k ih =>
    simp only [algTable, zero_mem_loads, ↓reduceIte]
    split
    · exact ih
    · exact le_trans ih (le_max_left _ _)

/-- Immediate structural safety of converting the maximum to a natural number. -/
lemma algMaximum_eq_value {m : ℕ} (I : Instance m) :
    algMaximum I = (algValue I : WithBot ℕ) := by
  have h : (0 : WithBot ℕ) ≤ algMaximum I :=
    le_trans (zero_reachable I I.n) (Finset.le_sup (f := algTable I I.n) (zero_mem_loads I))
  unfold algValue
  generalize he : algMaximum I = z at *
  cases z with
  | bot => exact False.elim (by simp at h)
  | coe v => rfl

end LawlerCompress.TardyJobs


