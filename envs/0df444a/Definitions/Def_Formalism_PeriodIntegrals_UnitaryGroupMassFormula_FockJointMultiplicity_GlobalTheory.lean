-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:38.342958+00:00
-- url     : https://prove2.me/theorems/93e40aa1-e02d-435b-aa04-b91cc9f45a36
-- title:
--   Global Theory
-- statement:
--   Definitions and structural lemmas for Global Theory, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/GlobalTheory.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FJM
def nP {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => 0 < f i).card
def nN {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => f i < 0).card
theorem nP_le_nW {n : ℕ} (f : Fin n → ℚ) : nP f ≤ n := by
  unfold nP
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le
theorem nN_le {n : ℕ} (f : Fin n → ℚ) : nN f ≤ n := by
  unfold nN
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le
section Blocks
variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
def leftWeightFirst : Fin p → ℚ := fun i => nu1 p q r s μ (.inl i)
def leftWeightSecond : Fin q → ℚ := fun j => nu1 p q r s μ (.inr j)
def rightWeightFirst : Fin r → ℚ := fun k => nu2 p q r s μ' (.inl k)
def rightWeightSecond : Fin s → ℚ := fun l => nu2 p q r s μ' (.inr l)
def ιA : Fin (nP (leftWeightFirst p q r s μ)) × Fin (nP (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.castLE (nP_le_nW _) x.1), .inl (Fin.castLE (nP_le_nW _) x.2))
def ιB : Fin (nN (leftWeightFirst p q r s μ)) × Fin (nN (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.rev (Fin.castLE (nN_le _) x.1)), .inr (Fin.rev (Fin.castLE (nN_le _) x.2)))
def ιC : Fin (nP (leftWeightSecond p q r s μ)) × Fin (nP (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.castLE (nP_le_nW _) x.1), .inr (Fin.castLE (nP_le_nW _) x.2))
def ιD : Fin (nN (leftWeightSecond p q r s μ)) × Fin (nN (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.rev (Fin.castLE (nN_le _) x.1)), .inl (Fin.rev (Fin.castLE (nN_le _) x.2)))
def αA : Fin (nP (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊leftWeightFirst p q r s μ (Fin.castLE (nP_le_nW _) i)⌋₊
def βA : Fin (nP (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊rightWeightFirst p q r s μ' (Fin.castLE (nP_le_nW _) k)⌋₊
def αB : Fin (nN (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊-leftWeightFirst p q r s μ (Fin.rev (Fin.castLE (nN_le _) i))⌋₊
def βB : Fin (nN (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊-rightWeightSecond p q r s μ' (Fin.rev (Fin.castLE (nN_le _) l))⌋₊
def αC : Fin (nP (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊leftWeightSecond p q r s μ (Fin.castLE (nP_le_nW _) j)⌋₊
def βC : Fin (nP (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊rightWeightSecond p q r s μ' (Fin.castLE (nP_le_nW _) l)⌋₊
def αD : Fin (nN (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊-leftWeightSecond p q r s μ (Fin.rev (Fin.castLE (nN_le _) j))⌋₊
def βD : Fin (nN (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊-rightWeightFirst p q r s μ' (Fin.rev (Fin.castLE (nN_le _) k))⌋₊
def vLine : Pol p q r s :=
  shapeProd (Matrix.of fun i k => (X (ιA p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αA p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιB p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αB p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιC p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αC p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιD p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αD p q r s μ))
end Blocks
def IsBlockHighestWeight {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) ∧ (∀ c d : Fin n, c < d → bCol ι c d P = 0) ∧
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) ∧
  (∀ i, 0 < α i) ∧ (∀ k, 0 < β k)
def HypA : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιA p q r s μ μ') (αA p q r s μ) (βA p q r s μ') P
def HypB : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιB p q r s μ μ') (αB p q r s μ) (βB p q r s μ') P
def HypC : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιC p q r s μ μ') (αC p q r s μ) (βC p q r s μ') P
def HypD : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιD p q r s μ μ') (αD p q r s μ) (βD p q r s μ') P
def CoverJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    l ∈ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
      Set.range (ιD p q r s μ μ')
def SqFacts {m n : ℕ} (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  m = n ∧ Antitone α ∧ ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k
def BlockFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  SqFacts (αA p q r s μ) (βA p q r s μ') ∧ SqFacts (αB p q r s μ) (βB p q r s μ') ∧
  SqFacts (αC p q r s μ) (βC p q r s μ') ∧ SqFacts (αD p q r s μ) (βD p q r s μ')
def SegFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)
def IntFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ a, ((⌊nu1 p q r s μ a⌋ : ℤ) : ℚ) = nu1 p q r s μ a) ∧ (∀ c, ((⌊nu2 p q r s μ' c⌋ : ℤ) : ℚ) = nu2 p q r s μ' c)
def ShapeFromFacts : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  BlockFacts p q r s μ μ' → SegFacts p q r s μ μ' → IntFacts p q r s μ μ' → JointShape p q r s μ μ'
end PI.FJM


