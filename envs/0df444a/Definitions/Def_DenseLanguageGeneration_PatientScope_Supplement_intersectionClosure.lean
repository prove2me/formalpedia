-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_intersectionClosure
-- name    : DenseLanguageGeneration_PatientScope_Supplement_intersectionClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:54.684901+00:00
-- url     : https://prove2.me/theorems/862a0680-f05a-4e07-bfdd-624cfb9706c2
-- title:
--   The ordered infinite finite-intersection family
-- statement:
--   Let $\mathcal L=(L_1,L_2,\ldots)$ be the known family of infinite languages. For a positive integer binary code $b$, define
--
--   $$L'_b=\bigcap_{j:\,\text{bit}_{j-1}(b)=1}L_j.$$
--
--   Thus the code $5=101_2$ denotes $L_1\cap L_3$. Discard precisely those intersections that are finite, then list all remaining codes in increasing order to form $\mathcal L'$. The singleton codes $2^{j-1}$ denote $L_j$ itself, so infinitely many codes remain even if some languages coincide. The patient-scope algorithm for partial enumeration is the published generator applied to this constructed family.
--
--   For an arbitrary set $S$ and infinite language $K$, also put
--
--   $$\underline d(S\mid K)=\liminf_{n\to\infty}\frac{|S\cap[n]|}{|K\cap[n]|},$$
--
--   with zero ratio at a zero denominator. This is the relative lower density used in Theorem B.3. The construction never assumes all finite intersections are infinite and never uses the secret target or enumerated subset.
--
--   **Formalization Note** Family index $j$ is zero-based, and code $c$ represents the source's positive code $c+1$. `Nat.nth` enumerates the retained codes increasingly; its membership proof follows from the singleton codes. The auxiliary proved lemmas establish only this subtype construction.
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Appendix B, printed pp.39–41 (PDF pp.41–43), especially the construction before Lemma B.2 on printed p.40 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter
noncomputable section

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Appendix B (printed p.40 / PDF p.42). L′_I = ⋂_{j ∈ I} L_j for the nonempty
finite index set I written as a 1-based indicator binary. With the zero-based
`Family` (index j is the paper's L_{j+1}), code c is the paper's code c+1:
L′_c = ⋂ {L j | bit j of c+1 is set}. Example: c = 4 (paper 5 = 101₂) is L 0 ∩ L 2. -/
def interCode (L : Family) (c : ℕ) : Set ℕ+ :=
  {x | ∀ j : ℕ, Nat.testBit (c + 1) j = true → x ∈ (L j).val}

/-- The codes kept by the paper: finite intersections are discarded. -/
def KeptCode (L : Family) (c : ℕ) : Prop := (interCode L c).Infinite

/-- The single-bit code 2^j − 1 (paper 2^j) is the language L j itself. -/
theorem interCode_two_pow_sub_one (L : Family) (j : ℕ) :
    interCode L (2 ^ j - 1) = (L j).val := by
  have h : 2 ^ j - 1 + 1 = 2 ^ j := Nat.sub_add_cancel Nat.one_le_two_pow
  ext x
  simp only [interCode, h, Nat.testBit_two_pow, decide_eq_true_eq, Set.mem_ofPred_eq]
  constructor
  · intro hx; exact hx j rfl
  · rintro hx j' rfl; exact hx

/-- Infinitely many codes are kept (every L j appears), so re-indexing is total. -/
theorem keptCode_infinite (L : Family) : {c | KeptCode L c}.Infinite := by
  have hinj : Function.Injective (fun j : ℕ => 2 ^ j - 1) := by
    intro a b hab
    have h1 : 2 ^ a - 1 + 1 = 2 ^ b - 1 + 1 := by simp only at hab; rw [hab]
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel Nat.one_le_two_pow] at h1
    exact Nat.pow_right_injective le_rfl h1
  refine Set.infinite_of_injective_forall_mem hinj (fun j => ?_)
  show (interCode L (2 ^ j - 1)).Infinite
  rw [interCode_two_pow_sub_one]
  exact (L j).property

/-- The n-th kept code in increasing order (zero-based n). -/
def closureCode (L : Family) (n : ℕ) : ℕ := Nat.nth (KeptCode L) n

/-- Appendix B: the collection ℒ′ fed to the patient-scope algorithm: the infinite
finite intersections L′_c listed in increasing code order, finite ones discarded. -/
def intersectionClosure (L : Family) : Family := fun n =>
  ⟨interCode L (closureCode L n), Nat.nth_mem_of_infinite (keptCode_infinite L) n⟩

/-- Appendix B / Theorem B.3: lower density of S in the language K,
liminf_n |S ∩ [n]| / |K ∩ [n]|, ratio 0 at a zero denominator. -/
def relativeLowerDensity (S : Set ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) : ℝ :=
  Filter.liminf (fun n => (prefixCount S n : ℝ) / (prefixCount K.val n : ℝ)) atTop

end DenseLanguageGeneration.PatientScope.Supplement


