-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10
-- name    : QAlgorithms_Papers_Independent_Gap20_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:22:59.431719+00:00
-- url     : https://prove2.me/theorems/91b4e4fd-5784-4341-b760-b528d7012537
-- title:
--   Definitions for An additive and operational entanglement measure: conditional entanglement of mutual information
-- statement:
--   The objects the formalized statements of *An additive and operational entanglement measure: conditional entanglement of mutual information* (arXiv:0804.3683) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pairedDifference`: PDF pp.2,4: the symmetric paired information increment, with exactly one primed register per party. `info .total` uses sum of individual entropies minus joint entropy; it is not the dual total correlation.
--   - `cemiValues`: Definition 1, PDF p.2, and multipartite definition, p.4: all normalized paired extensions with the required honest marginal, in arbitrary positive finite ancillary dimensions. The dimensions have no common cap.
--   - `cemi`: Definition 1, PDF p.2, and p.4: CEMI is the half-infimum, without an attainment assertion. For the density matrices on nonzero finite spaces used below the value set is nonempty (one-dimensional primes suffice) and bounded below by zero (data processing). On invalid matrices the real sInf default is irrelevant; no theorem evaluates it on an invalid matrix.
--   - `asTwo`: PDF p.2: transport an ordinary A x B matrix to the two-register basis, without taking a partial trace or changing either party.
--   - `bipartiteCemi`: Definition 1, PDF p.2: bipartite CEMI, using the same half-infimum as cemi.
--   - `cemiFunctional`: PDF pp.2--4: CEMI on the accepted bundled normalized finite states.
--   - `regroupedProduct`: Proposition 1, PDF p.3: construct rho_AB tensor sigma_CD and regroup to AC:BD. Each entry is the product of the two original entries.
--   - `marginalCD`: PDF p.3, equation (5): retain CD from the same general state on ACBD.
--   - `routeDifference`: PDF pp.3--4: five named registers, indexed 0=A, 1=A', 2=B, 3=B', 4=E. This is the information increment of the actual AA'BB' marginal, since info traces out all unnamed registers, including E.
--   - `routeI`: PDF p.4, Fig.3, route I: half the sum of the displayed two CMIs. The second conditioning register is the actual joint system EA.
--   - `routeII`: PDF p.4, Fig.3, route II: inward AA', zero-cost inward B, then outward A'. This is the displayed entropic charge, not a minimum over all protocols.
--   - `twoRegisterMarginal`: PDF pp.3--4: retain two specified distinct physical registers. All other registers are traced out, with their bra and ket indices equal.
--   - `trivialPairedExtension`: PDF p.2: trivial one-dimensional paired ancillary registers.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, https://arxiv.org/abs/0804.3683v2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-!
Yang--Horodecki--Wang, arXiv:0804.3683v2, PDF pp.2--4.
Finite nonzero local Hilbert spaces; entropy in bits. Accepted library imports
supply actual density matrices, reductions, finite adaptive LOCC, pure formation,
and operational entanglement cost. New definitions are confined to this paper.
The operational signed-minimum claims are deferred, not defined by an entropy.
Compilation is pending the batch mechanical-check stage.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,4: the symmetric paired information increment, with exactly one
primed register per party. `info .total` uses sum of individual entropies minus
joint entropy; it is not the dual total correlation. -/
def pairedDifference {n : ℕ} {D F : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (omega : Matrix (RegisterBasis (fun i => D i × F i))
      (RegisterBasis (fun i => D i × F i)) ℂ) : ℝ :=
  info .total omega (singleParties n) ∅ -
    info .total (primedMarginal omega) (singleParties n) ∅

/-- Definition 1, PDF p.2, and multipartite definition, p.4: all normalized
paired extensions with the required honest marginal, in arbitrary positive
finite ancillary dimensions. The dimensions have no common cap. -/
def cemiValues {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : Set ℝ :=
  {v | ∃ d : Fin n → ℕ, (∀ i, 0 < d i) ∧
    ∃ omega : Matrix (RegisterBasis (fun i => D i × Fin (d i)))
      (RegisterBasis (fun i => D i × Fin (d i))) ℂ,
      IsDensityMatrix omega ∧ unprimedMarginal omega = rho ∧
      v = pairedDifference omega / 2}

/-- Definition 1, PDF p.2, and p.4: CEMI is the half-infimum, without an
attainment assertion. For the density matrices on nonzero finite spaces used
below the value set is nonempty (one-dimensional primes suffice) and bounded
below by zero (data processing). On invalid matrices the real sInf default is
irrelevant; no theorem evaluates it on an invalid matrix. -/
def cemi {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  sInf (cemiValues rho)

/-- PDF p.2: canonical two-party type family, preserving the A:B cut. -/
instance twoPartyFintype {A B : Type} [Fintype A] [Fintype B] :
    (i : Fin 2) → Fintype ((![A, B] : Fin 2 → Type) i) := by
  exact Fin.cases (inferInstance : Fintype A)
    (Fin.cases (inferInstance : Fintype B) (fun i => Fin.elim0 i))

/-- PDF p.2: transport an ordinary A x B matrix to the two-register basis,
without taking a partial trace or changing either party. -/
def asTwo {A B : Type} (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (RegisterBasis (![A, B] : Fin 2 → Type))
      (RegisterBasis (![A, B] : Fin 2 → Type)) ℂ :=
  fun x y => rho (x 0, x 1) (y 0, y 1)

/-- Definition 1, PDF p.2: bipartite CEMI, using the same half-infimum as cemi. -/
def bipartiteCemi {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  cemi (asTwo rho)

/-- PDF pp.2--4: CEMI on the accepted bundled normalized finite states. -/
def cemiFunctional {n : ℕ} (s : FiniteState n) : ℝ := cemi s.rho

/-- Proposition 1, PDF p.3: construct rho_AB tensor sigma_CD and regroup to
AC:BD. Each entry is the product of the two original entries. -/
def regroupedProduct {A B C D : Type}
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ :=
  fun x y => rho (x.1.1, x.2.1) (y.1.1, y.2.1) *
    sigma (x.1.2, x.2.2) (y.1.2, y.2.2)

/-- PDF p.3, equation (5): retain CD from the same general state on ACBD. -/
def marginalCD {A B C D : Type} [Fintype A] [Fintype B]
    (tau : Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ) :
    Matrix (C × D) (C × D) ℂ :=
  fun x y => ∑ a, ∑ b, tau ((a, x.1), (b, x.2)) ((a, y.1), (b, y.2))

/-- PDF pp.3--4: five named registers, indexed 0=A, 1=A', 2=B, 3=B', 4=E.
This is the information increment of the actual AA'BB' marginal, since info
traces out all unnamed registers, including E. -/
def routeDifference {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  info .total omega ![{0, 1}, {2, 3}] ∅ -
    info .total omega ![{1}, {3}] ∅

/-- PDF p.4, Fig.3, route I: half the sum of the displayed two CMIs.
The second conditioning register is the actual joint system EA. -/
def routeI {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  (info .total omega ![{2, 3}, {0}] {4} +
    info .total omega ![{1}, {2}] {4, 0}) / 2

/-- PDF p.4, Fig.3, route II: inward AA', zero-cost inward B, then outward
A'. This is the displayed entropic charge, not a minimum over all protocols. -/
def routeII {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  (info .total omega ![{2, 3}, {0, 1}] ∅ + 0 -
    info .total omega ![{1}, {3}] ∅) / 2

/-- PDF pp.3--4: retain two specified distinct physical registers.
All other registers are traced out, with their bra and ket indices equal. -/
def twoRegisterMarginal {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (i j : Fin n) :
    Matrix (D i × D j) (D i × D j) ℂ :=
  fun a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    if x i = a.1 ∧ x j = a.2 ∧ y i = b.1 ∧ y j = b.2 ∧
      (∀ k, k ≠ i → k ≠ j → x k = y k) then omega x y else 0

/-- PDF p.2: trivial one-dimensional paired ancillary registers. -/
def trivialPairedExtension {n : ℕ} {D : Fin n → Type}
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix (RegisterBasis (fun i => D i × Fin 1))
      (RegisterBasis (fun i => D i × Fin 1)) ℂ :=
  fun x y => rho (fun i => (x i).1) (fun i => (y i).1)

/-- Sanity: trivial primed registers do not change the honest marginal. -/
example {n : ℕ} {D : Fin n → Type} (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    unprimedMarginal (trivialPairedExtension rho) = rho := by
  ext x y
  simp [unprimedMarginal, trivialPairedExtension]

/-- Sanity: the two-party adapter preserves arbitrary off-diagonal entries. -/
example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (x y : RegisterBasis (![A, B] : Fin 2 → Type)) :
    asTwo rho x y = rho (x 0, x 1) (y 0, y 1) := rfl

/-- Sanity: the product is grouped as AC:BD, including coherences. -/
example {A B C D : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (C × D) (C × D) ℂ) (a a2 : A) (b b2 : B)
    (c c2 : C) (d d2 : D) :
    regroupedProduct rho sigma ((a, c), (b, d)) ((a2, c2), (b2, d2)) =
      rho (a, b) (a2, b2) * sigma (c, d) (c2, d2) := rfl

/-- Sanity: the subtraction in route II has the source's outward sign. -/
example {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    routeII omega = (info .total omega ![{2, 3}, {0, 1}] ∅ -
      info .total omega ![{1}, {3}] ∅) / 2 := by
  simp only [routeII, add_zero]

end QAlgorithms.Papers.Independent.Gap20.P10


