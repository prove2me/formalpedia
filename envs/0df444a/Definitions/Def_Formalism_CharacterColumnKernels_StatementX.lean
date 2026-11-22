-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementX
-- name    : Formalism_CharacterColumnKernels_StatementX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:42.864718+00:00
-- url     : https://prove2.me/theorems/8200b249-d3a2-4e6d-9ba1-40829e6305e7
-- title:
--   Statement X
-- statement:
--   Definitions and structural lemmas for Statement X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementX.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.NG
def StatHomQuot : Prop :=
  ∀ (R O M NN : Type*) [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] [AddCommGroup NN] [Module R NN]
    (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R) (n : g → NN),
    Submodule.span R (Set.range n) = ⊤ → (∀ i, ∑ j, Θ i j • n j = 0) →
    (∀ φ : NN →ₗ[R] M, (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ)) ∧
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) ∧
    Module.length O (NN →ₗ[R] M) ≤ Module.length O (LinearMap.ker (relMap O M Θ))
def StatDeltaValO : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) [Fact l.Prime],
    l ≠ 2 → ¬ IsUnit (l : O) → ∀ (u : Oˣ) (w t : ℕ),
    IsDiscreteValuationRing.addVal O
        (delta (fun i : Fin (t + 1) => (u : O) * (1 + (l : O)) ^ (w + (i : ℕ)))) =
      IsDiscreteValuationRing.addVal O (l : O) * ((t + padicValNat l t.factorial : ℕ) : ℕ∞)
def matEnd (O M : Type*) [CommRing O] [AddCommGroup M] [Module O M] (d : Type*) [Fintype d]
    [DecidableEq d] : Matrix d d O →+* Module.End O (d → M) where
  toFun A := relMap O M A
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  map_mul' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    show (∑ j, (A * B) i j • v j) = ∑ k, A i k • ∑ j, B k j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap]
  map_add' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, add_smul, Finset.sum_add_distrib]
def LatQ {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] [DecidableEq d] (_ρ : R →+* Matrix d d O) : Type _ := d → KO O
section LatQ
variable {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (d : Type*) [Fintype d] [DecidableEq d] (ρ : R →+* Matrix d d O)
instance : AddCommGroup (LatQ O d ρ) := inferInstanceAs (AddCommGroup (d → KO O))
instance : Module O (LatQ O d ρ) := inferInstanceAs (Module O (d → KO O))
instance : Module R (LatQ O d ρ) :=
  Module.compHom (d → KO O) ((matEnd O (KO O) d).comp ρ)
end LatQ
def StatKerHomBlock : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (Θ : Matrix g g R),
    Module.length O (LinearMap.ker (matQ O (bigMat ρ Θ))) =
      Module.length O (Coker Θ →ₗ[R] LatQ O d ρ)
def StatEopCorner : Prop :=
  ∀ (T A V : Type*) [CommRing T] [Ring A] [Algebra T A] [AddCommGroup V] [Module A V]
    (e x : A) (t : ℕ) (r : Fin (t + 1) → T), e * e = e → e * x = x → x * e = x →
    e * aeval x (∏ i, (X - C (r i))) * e = 0 →
    (x * (e * Eop x r * e) = algebraMap T A (r 0) * (e * Eop x r * e)) ∧
    ((e * Eop x r * e) * (e * Eop x r * e) = algebraMap T A (delta r) * (e * Eop x r * e)) ∧
    (e * (e * Eop x r * e) * e = e * Eop x r * e) ∧
    (∀ v : V, e • v = 0 → (e * Eop x r * e) • v = 0)
def EopAt {T A : Type*} [CommRing T] [Ring A] [Algebra T A] (x : A) {t : ℕ} (r : Fin (t + 1) → T)
    (i : Fin (t + 1)) : A :=
  aeval x (∏ k ∈ univ.erase i, (X - C (r k)))
def StatEijZero : Prop :=
  ∀ (T A : Type*) [CommRing T] [Ring A] [Algebra T A] (x : A) (t : ℕ) (r : Fin (t + 1) → T),
    Roots x r → ∀ i j : Fin (t + 1), i ≠ j → EopAt x r i * EopAt x r j = 0
def StatLenCoker : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) =
      IsDiscreteValuationRing.addVal O A.det
def StatKerHomRect : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (P : Matrix m g R),
    Module.length O (LinearMap.ker (relMap O (KO O)
        (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2))) =
      Module.length O (Coker P →ₗ[R] LatQ O d ρ)
end Formalism.NG


