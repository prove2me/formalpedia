-- Prove2me | Definitions.Def_PermSymQuery_Quadratic_Sampled
-- name    : PermSymQuery_Quadratic_Sampled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:18.341923+00:00
-- url     : https://prove2.me/theorems/8ac7c771-ace4-4f2c-9a15-51c5277e9da1
-- title:
--   Sampled compressed permutation databases and restriction embedding
-- statement:
--   Let $N,s$ be natural numbers, $i\in[N]$, and let $D,H$ be partial injections from $[N]$ to itself. The published database Hilbert space has the partial injections as an orthonormal basis. Write $|D|$ for the number of records and $\operatorname{im}D\subseteq S$ for validity in a sample $S$.
--
--   The sampled space is the span of valid basis pairs $|S,D\rangle$, where $|S|=s$ and $\operatorname{im}D\subseteq S$, inside the Euclidean space on all sample/database pairs. For $i\notin\operatorname{dom}H$, the sampled compression exchanges $|H\rangle$ with the normalized uniform sum of $|H\cup\{i\mapsto y\}\rangle$ over $y\in S\setminus\operatorname{im}H$ and fixes the remaining directions in that block. If there is no available extension, the block is fixed by the identity. Databases whose images leave $S$ are also fixed; they are outside the source's sampled space and are never reached from it. The direct sum over samples gives $\widehat C_i$.
--
--   Lookup leaves the sample and database fixed and swaps answer labels $\bot$ and $D(i)$ when a record exists, otherwise doing nothing. Its full and sampled forms are $L_i^N$ and $\widehat L_i$. With identity on the answer register understood,
--   $$\widehat O_i=\widehat C_i\widehat L_i\widehat C_i.$$
--   These sampled operators preserve the valid sampled subspace. The restriction embedding is the linear extension of
--   $$J_s|D\rangle=\binom{N-|D|}{s-|D|}^{-1/2}\sum_{|S|=s,\ \operatorname{im}D\subseteq S}|S,D\rangle.$$
--   This formula is used only for $|D|\le s\le N$; outside that domain the extension is explicitly zero. The combined map is $W=J_sV_N$, with $V_N$ the concrete published Carolan–Majenz map, not a variable constrained by an isometry hypothesis. The block projector selects $|H\rangle$ and every admissible one-record extension at address $i$.
--
--   The definitions provide the exact operators used in Lemmas 3.2 and 3.3. They do not assume the Open compressed-oracle approximation theorem, and they do not encode any proposed norm bound as part of a definition.
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), §§3.2–3.4, Eq. (3) and compression-block definition, PDF p. 11 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

open CompPermOracle

/-- A database has its image in S exactly when every occupied label is in S. -/
def ImageIn {N : ℕ} (D : PartialPerm N) (S : Finset (Fin N)) : Prop :=
  ∀ y, ¬ NotInIm D y → y ∈ S

/-- The ambient sampled space. The valid subspace is specified by `sampledSpace`. -/
abbrev SampleBasis (N s : ℕ) := Sample N s × PartialPerm N

/-- ⊕_{|S|=s} |S⟩ ⊗ L_S, embedded into the ambient product basis. -/
noncomputable def sampledSpace (N s : ℕ) : Submodule ℂ (Hil (SampleBasis N s)) :=
  Submodule.span ℂ {v | ∃ p : SampleBasis N s, ImageIn p.2 p.1.val ∧ v = ket p}

/-- Normalized extension state with labels restricted to S. When no extension is available
this helper is zero; `sampleCompress` never uses it in an exhausted block. -/
noncomputable def samplePlus {N : ℕ} (i : Fin N) (S : Finset (Fin N)) (H : PartialPerm N) :
    Hil (PartialPerm N) := by
  classical
  let labels := S.filter (fun y => NotInIm H y)
  exact if labels.Nonempty then
    ((Real.sqrt (labels.card : ℝ))⁻¹ : ℂ) • ∑ y ∈ labels, ket (addPair H i y)
  else 0

/-- C_i^S. Reflection blocks with no extension are omitted, hence fixed by the identity.
Invalid databases (image outside S) are fixed too; they are never reached from the valid subspace. -/
noncomputable def sampleCompress {N : ℕ} (i : Fin N) (S : Finset (Fin N)) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) := by
  classical
  exact 1 - ∑ H ∈ Finset.univ.filter (fun H : PartialPerm N =>
      NotInDom H i ∧ ImageIn H S ∧ (S.filter (fun y => NotInIm H y)).Nonempty),
    ketBra (ket H - samplePlus i S H) (ket H - samplePlus i S H)

/-- Ĉ_i, direct sum over the fixed sample label. Preserves `sampledSpace`. -/
noncomputable def hatC {N s : ℕ} (i : Fin N) :
    Hil (SampleBasis N s) →L[ℂ] Hil (SampleBasis N s) := by
  classical
  exact controlled (fun S : Sample N s => sampleCompress i S.val)

/-- L_i^N, literal database lookup of §3.2; no compression or adjoint convention is hidden. -/
noncomputable def lookupN {N : ℕ} (i : Fin N) :
    Hil (Ans N × PartialPerm N) →L[ℂ] Hil (Ans N × PartialPerm N) := by
  classical
  exact opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) (assertLBot i) +
    ∑ y : Fin N, opTensor (swapOp y) (assertL i y)

/-- L̂_i. Lookup keeps both the sample and database labels fixed, preserving the valid subspace. -/
noncomputable def hatL {N s : ℕ} (i : Fin N) :
    Hil (Ans N × SampleBasis N s) →L[ℂ] Hil (Ans N × SampleBasis N s) := by
  classical
  exact ∑ p : Ans N × SampleBasis N s,
    ketBra (ket ((match p.2.2 i with
      | none => p.1
      | some y => Equiv.swap none (some y) p.1), p.2)) (ket p)

/-- Ô_i = Ĉ_i L̂_i Ĉ_i, with identity on the answer register implicit in the paper. -/
noncomputable def hatO {N s : ℕ} (i : Fin N) :
    Hil (Ans N × SampleBasis N s) →L[ℂ] Hil (Ans N × SampleBasis N s) := by
  classical
  let C := opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) (hatC (s := s) i)
  exact C.comp ((hatL i).comp C)

/-- J_s|D⟩, (3), extended by zero when |D| > s or s > N. Its nonzero coordinates
are valid sample/database pairs. All theorem uses are within the source's domain. -/
noncomputable def restrictBasis {N : ℕ} (s : ℕ) (D : PartialPerm N) :
    Hil (SampleBasis N s) := by
  classical
  exact if size D ≤ s ∧ s ≤ N then
    ((Real.sqrt (Nat.choose (N - size D) (s - size D) : ℝ))⁻¹ : ℂ) •
      ∑ S : Sample N s, if ImageIn D S.val then ket (S, D) else 0
  else 0

/-- Total linear extension of J_s from (3), zero on higher database levels. -/
noncomputable def restrictJ (N s : ℕ) :
    Hil (PartialPerm N) →L[ℂ] Hil (SampleBasis N s) := by
  classical
  exact ∑ D : PartialPerm N, ketBra (restrictBasis s D) (ket D)

/-- W = J_s V_N with V_N the concrete published Vtmap, never an assumed isometry. -/
noncomputable def sampledW (N s : ℕ) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (SampleBasis N s) :=
  (restrictJ N s).comp (Vtmap N)

/-- Orthogonal projector onto the entire compression block based at H. -/
noncomputable def blockProj {N : ℕ} (i : Fin N) (H : PartialPerm N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) := by
  classical
  exact ∑ D ∈ Finset.univ.filter (fun D : PartialPerm N =>
    D = H ∨ ∃ y ∈ freeIm H, D = addPair H i y), ketBra (ket D) (ket D)

end PermSymQuery.Quadratic


