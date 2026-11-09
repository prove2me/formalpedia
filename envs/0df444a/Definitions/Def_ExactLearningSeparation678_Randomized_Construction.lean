-- Prove2me | Definitions.Def_ExactLearningSeparation678_Randomized_Construction
-- name    : ExactLearningSeparation678_Randomized_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:21.255993+00:00
-- url     : https://prove2.me/theorems/2a2802fe-d6fb-4e7a-b943-804d317a0291
-- title:
--   Definition 3.1 — finite-field concepts and actual query complexities
-- statement:
--   For an integer $m\ge2$, put $t=2^m$ and $F=\mathbb F_{t^6}$. A chosen binary basis identifies $F$ with $\mathbb F_2^{6m}$. The map $\operatorname{trunc}$ keeps the first $2m$ coordinates, and $\langle b,a\rangle$ is the binary coordinate dot product. For arbitrary $a=(a_0,\ldots,a_{t-1})\in F^t$ and $s\in F$, let $P(X)=X^t+\sum_{j=0}^{t-1}a_jX^j$ and $P_{\rm trunc}=\operatorname{trunc}\circ P$.
--
--   The coordinate domain is the tagged disjoint union
--   $$X_t=(F\times F\times\mathbb F_2^{2m})\sqcup(F\times\{0,\ldots,t-1\}\times F).$$
--   The concept is given by
--   $$c_{P,s}(\mathrm{blk},x,c,z)=\mathbf1[z=P_{\rm trunc}(c+xs)],\qquad
--   c_{P,s}(\mathrm{sheet},u,j,b)=\mathbf1[u=s]\langle b,a_j\rangle.$$
--   The class $C_t$ is the image of all parameter pairs as Boolean functions, including all-zero lower coefficients. Define $N_t=t^{14}+t^{13}$. The quantities $Q_t$ and $R_t$ are the published quantum and randomized exact-learning minima, with worst-case success at least $2/3$ on every member of $C_t$. The Fourier exceptional mass is $t^{-12}\sum_z|P_{\rm trunc}^{-1}(z)|^2$.
--
--   These objects are shared by every fact and learning bound in the mission. Selecting a preimage of a concept defines its output parameters; uniqueness is left to Fact 3.4.
--
--   **Formalization Note** The basis is constructed from the finite extension's dimension. Labels use $\mathbb F_2$ coordinates, and row indices begin at zero. The published name `classicalExactComplexity` denotes randomized $R$, despite its name. No runtime or gate restriction is imposed.
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Definition 3.1, p.17; exact learning model, p.2; Eq. (11), p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Learning

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Definition 3.1, p.17: t = 2^m with m ≥ 2. -/
abbrev Size := {m : ℕ // 2 ≤ m}

def t (m : Size) : ℕ := 2 ^ m.val
abbrev F (m : Size) := GaloisField 2 (6 * m.val)

noncomputable instance fieldFintype (m : Size) : Fintype (F m) := Fintype.ofFinite _
noncomputable instance fieldDecidableEq (m : Size) : DecidableEq (F m) := Classical.decEq _

/-- A genuine binary basis, chosen from the finite extension, rather than a free coordinate map. -/
noncomputable def binaryBasis (m : Size) : Module.Basis (Fin (6 * m.val)) (ZMod 2) (F m) :=
  Module.finBasisOfFinrankEq (ZMod 2) (F m)
    (GaloisField.finrank 2 (by have := m.property; omega))

abbrev Label (m : Size) := Fin (2 * m.val) → ZMod 2
abbrev Coeff (m : Size) := Fin (t m) → F m
abbrev Parameters (m : Size) := Coeff m × F m

/-- First 2m of the 6m binary coordinates. -/
noncomputable def trunc (m : Size) (v : F m) : Label m :=
  fun i => (binaryBasis m).repr v ⟨i.val, by have := i.isLt; omega⟩

/-- Binary coordinate dot product, not field multiplication. -/
noncomputable def dot (m : Size) (v w : F m) : Bool :=
  decide ((∑ i : Fin (6 * m.val),
    (binaryBasis m).repr v i * (binaryBasis m).repr w i) = 1)

/-- The full monic degree-t polynomial, with every lower coefficient permitted. -/
noncomputable def polynomial (m : Size) (a : Coeff m) : Polynomial (F m) :=
  Polynomial.X ^ t m + ∑ j : Fin (t m), Polynomial.C (a j) * Polynomial.X ^ j.val

noncomputable def pTrunc (m : Size) (a : Coeff m) (y : F m) : Label m :=
  trunc m ((polynomial m a).eval y)

abbrev Domain (m : Size) :=
  (F m × F m × Label m) ⊕ (F m × Fin (t m) × F m)

/-- Both parts of Definition 3.1, with disjoint tags. -/
noncomputable def concept (m : Size) (p : Parameters m) : Domain m → Bool
  | .inl (x, c, z) => decide (z = pTrunc m p.1 (c + x * p.2))
  | .inr (u, j, b) => if u = p.2 then dot m b (p.1 j) else false

/-- Actual functions: no injectivity is built into the class. -/
noncomputable def conceptClass (m : Size) : Finset (Domain m → Bool) :=
  Finset.univ.image (concept m)

abbrev Concept (m : Size) := {c : Domain m → Bool // c ∈ conceptClass m}

/-- Chosen preimage of an output concept; Fact 3.4 proves it is unique. -/
noncomputable def outputParameters (m : Size) (c : Concept m) : Parameters m :=
  Classical.choose (show ∃ p, concept m p = c.val from by
    have h := Finset.mem_image.mp c.property
    rcases h with ⟨p, _, hp⟩
    exact ⟨p, hp⟩)

noncomputable def Q (m : Size) : ℕ := QAlgorithms.Learning.quantumExactComplexity (conceptClass m)
noncomputable def R (m : Size) : ℕ := QAlgorithms.Learning.classicalExactComplexity (conceptClass m)

def N (m : Size) : ℕ := (t m) ^ 14 + (t m) ^ 13

/-- Equation (11), p.21: actual Fourier exceptional mass from the fibers. -/
noncomputable def fourierFailure (m : Size) (a : Coeff m) : ℝ :=
  (∑ z : Label m,
    (((Finset.univ.filter (fun y => pTrunc m a y = z)).card : ℝ) ^ 2)) / (t m : ℝ) ^ 12

end ExactLearningSeparation678.Randomized


