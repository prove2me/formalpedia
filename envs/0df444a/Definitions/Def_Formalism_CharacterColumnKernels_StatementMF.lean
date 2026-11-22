-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
-- name    : Formalism_CharacterColumnKernels_StatementMF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:28.740694+00:00
-- url     : https://prove2.me/theorems/8c5a25e7-f9ba-44de-b11a-c324e67e8a2b
-- title:
--   Statement MF
-- statement:
--   Definitions and structural lemmas for Statement MF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementMF.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
universe u
def StatRankOneDet : Prop :=
  ∀ (K : Type*) [Field K] (n : Type) [Fintype n] [DecidableEq n] (ε : Matrix n n K),
    IsIdempotentElem ε → ε.rank = 1 → ∀ c : K, (1 - ε + c • ε).det = c
def StatRankDet : Prop :=
  ∀ (K : Type*) [Field K] (n : Type) [Fintype n] [DecidableEq n] (ε : Matrix n n K),
    IsIdempotentElem ε → ∀ c : K, (1 - ε + c • ε).det = c ^ ε.rank
def blockOf {g n K : Type*} (M : Matrix g g (Matrix n n K)) : Matrix (g × n) (g × n) K :=
  fun p q => M p.1 q.1 p.2 q.2
def StatTriRankOneDet : Prop :=
  ∀ (K : Type*) [Field K] (n : Type) [Fintype n] [DecidableEq n] (ι : Type)
    (ε : ι → Matrix n n K), (∀ i, IsIdempotentElem (ε i)) → (∀ i, (ε i).rank = 1) →
    ∀ (c : K) (g : ℕ) (idx : Fin g → ι) (M : Matrix (Fin g) (Fin g) (Matrix n n K)),
      (∀ j k, k < j → M j k = 0) → (∀ j, M j j = 1 - ε (idx j) + c • ε (idx j)) →
      (blockOf M).det = c ^ g
def StatTriRankDet : Prop :=
  ∀ (K : Type*) [Field K] (n : Type) [Fintype n] [DecidableEq n] (ι : Type)
    (ε : ι → Matrix n n K), (∀ i, IsIdempotentElem (ε i)) →
    ∀ (c : K) (g : ℕ) (idx : Fin g → ι) (M : Matrix (Fin g) (Fin g) (Matrix n n K)),
      (∀ j k, k < j → M j k = 0) → (∀ j, M j j = 1 - ε (idx j) + c • ε (idx j)) →
      (blockOf M).det = c ^ (∑ j, (ε (idx j)).rank)
def epsImg (O : Type*) {OO M : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ε : OO) : Submodule O M :=
  LinearMap.range (DistribSMul.toLinearMap O M ε)
def StatLenEps : Prop :=
  ∀ (O OO : Type*) (M : Type u) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ι : Type) [Fintype ι] (ε : ι → OO),
    (∀ i, IsIdempotentElem (ε i)) →
    (∀ (S : Type u) [AddCommGroup S] [Module OO S], IsSimpleModule OO S → ∃ i, ∃ s : S, ε i • s ≠ 0) →
    IsFiniteLength OO M →
    Module.length OO M ≤ ∑ i, Module.length O (epsImg O (M := M) (ε i))
def StatLenEpsSub : Prop :=
  ∀ (O OO M : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ι : Type) [Fintype ι] (ε : ι → OO),
    (∀ i, IsIdempotentElem (ε i)) →
    (∀ N₁ N₂ : Submodule OO M, N₁ ≤ N₂ → IsSimpleModule OO (N₂ ⧸ N₁.comap N₂.subtype) →
      ∃ i, ∃ s ∈ N₂, ε i • s ∉ N₁) →
    IsFiniteLength OO M →
    Module.length OO M ≤ ∑ i, Module.length O (epsImg O (M := M) (ε i))
def epsIdeal (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε : OO) :
    Submodule O OO :=
  LinearMap.range (LinearMap.mulLeft O ε)
def rightMulEps (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε a : OO) :
    epsIdeal O ε →ₗ[O] epsIdeal O ε where
  toFun x := ⟨x.1 * a, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y * a, by simp only [LinearMap.mulLeft_apply] at hy ⊢; rw [← mul_assoc, hy]⟩⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp
abbrev EpsDual (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
    (ε : OO) : Type _ :=
  epsIdeal O ε →ₗ[O] Q
section EpsDual
variable (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
  (ε : OO)
instance EpsDual.moduleOO : Module OO (EpsDual O OO Q ε) where
  smul a φ := (show epsIdeal O ε →ₗ[O] Q from φ).comp (rightMulEps O ε a)
  one_smul φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε 1 x) = φ x
    congr 1; ext; simp [rightMulEps]
  mul_smul a b φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε (a * b) x) = φ (rightMulEps O ε b (rightMulEps O ε a x))
    congr 1; ext; simp [rightMulEps, mul_assoc]
  smul_zero a := by
    refine LinearMap.ext fun x => ?_
    rfl
  smul_add a φ ψ := by
    refine LinearMap.ext fun x => ?_
    rfl
  add_smul a b φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε (a + b) x) = φ (rightMulEps O ε a x) + φ (rightMulEps O ε b x)
    rw [← map_add]; congr 1; ext; simp [rightMulEps, mul_add]
  zero_smul φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε 0 x) = 0
    have : rightMulEps O ε 0 x = 0 := by ext; simp [rightMulEps]
    rw [this, map_zero]
end EpsDual
def StatEpsAdj : Prop :=
  ∀ (O OO M Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO),
    IsIdempotentElem ε → [SMulCommClass OO O (EpsDual O OO Q ε)] →
    Nonempty ((M →ₗ[OO] EpsDual O OO Q ε) ≃ₗ[O] (epsImg O (M := M) ε →ₗ[O] Q))
def StatMatlis : Prop :=
  ∀ (O N : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N]
    [Module O N], IsFiniteLength O N →
    Module.length O (N →ₗ[O] KO O) = Module.length O N
def nnY {R Y S : Type*} [Ring R] [Ring S] [AddCommGroup Y] [Module R Y] (pr : R →+* S) :
    Submodule R Y :=
  Submodule.span R {z | ∃ x : R, pr x = 0 ∧ ∃ y : Y, z = x • y}
def nnYe {R Y S : Type*} [Ring R] [Ring S] [AddCommGroup Y] [Module R Y] (pr : R →+* S) (e : R) :
    Submodule R Y :=
  nnY pr ⊔ Submodule.span R (Set.range fun y : Y => (1 - e) • y)
def StatMultFreeGens : Prop :=
  ∀ (O : Type*) (R OO BB Y : Type u) [CommRing O] [IsLocalRing O] [Ring R] [Algebra O R]
    [Module.Finite O R] [Ring OO] [Ring BB] [AddCommGroup Y] [Module R Y] [Module.Finite R Y]
    (pr : R →+* OO × BB), Function.Surjective pr →
    (∀ x : R, pr x = 0 → ∀ r : R, IsUnit (1 + r * x)) →
    ∀ ϖ : O, ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ e : R, IsIdempotentElem e → pr e = (1, 0) →
    ∀ (ι : Type) (ε : ι → OO) (εt : ι → R), (∀ i, IsIdempotentElem (εt i)) →
      (∀ i, pr (εt i) = (ε i, 0)) → (∀ i, e * εt i * e = εt i) →
      (∀ (S : Type u) [AddCommGroup S] [Module R S], IsSimpleModule R S →
        (∀ x : R, pr x = 0 → ∀ s : S, x • s = 0) → (∀ s : S, e • s = s) →
        ∃ i, ∃ s : S, εt i • s ≠ 0) →
      IsFiniteLength R (Y ⧸ nnY (Y := Y) pr) →
      ∃ (g g' : ℕ) (w : Fin g → Y) (w' : Fin g' → Y) (Θ : Matrix (Fin g) (Fin g) R)
        (Θ' : Matrix (Fin g) (Fin g') R) (idx : Fin g → ι),
        (g : ℕ∞) = Module.length R (Y ⧸ nnYe (Y := Y) pr e) ∧
        Submodule.span R (Set.range w ∪ Set.range w' : Set Y) = ⊤ ∧
        (∀ k, e • w' k = 0) ∧ (∀ j, εt (idx j) • w j = w j) ∧
        (∀ j, ∑ k, Θ j k • w k + ∑ k, Θ' j k • w' k = 0) ∧
        (∀ j k, pr (Θ' j k) = 0) ∧
        (∀ j k, k < j → (pr (Θ j k)).1 = 0) ∧
        (∀ j, (pr (Θ j j)).1 = 1 - ε (idx j) + (pr (algebraMap O R ϖ)).1 * ε (idx j)) ∧
        (∀ j k, (pr (Θ j k)).2 = if j = k then 1 else 0)
def StatMultFree : Prop :=
  ∀ (O : Type*) (R OO BB Y : Type u) [CommRing O] [IsLocalRing O] [Ring R] [Algebra O R]
    [Module.Finite O R] [Ring OO] [Ring BB] [AddCommGroup Y] [Module R Y] [Module.Finite R Y] [Module O Y] [IsScalarTower O R Y]
    (pr : R →+* OO × BB), Function.Surjective pr →
    (∀ x : R, pr x = 0 → ∀ r : R, IsUnit (1 + r * x)) →
    ∀ ϖ : O, ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ e : R, IsIdempotentElem e → pr e = (1, 0) →
    ∀ (ι : Type) [Fintype ι] (ε : ι → OO) (εt : ι → R), (∀ i, IsIdempotentElem (εt i)) →
      (∀ i, pr (εt i) = (ε i, 0)) → (∀ i, e * εt i * e = εt i) →
      (∀ (S : Type u) [AddCommGroup S] [Module R S], IsSimpleModule R S →
        (∀ x : R, pr x = 0 → ∀ s : S, x • s = 0) → (∀ s : S, e • s = s) →
        ∃ i, ∃ s : S, εt i • s ≠ 0) →
      IsFiniteLength R (Y ⧸ nnY (Y := Y) pr) →
      ∀ (K : Type*) [Field K] [Algebra O K] (N : Type) [Fintype N] [DecidableEq N]
        (ιO : OO →+* Matrix N N K), (∀ i, (ιO (ε i)).rank = 1) →
        ιO ((pr (algebraMap O R ϖ)).1) = algebraMap O K ϖ • (1 : Matrix N N K) →
      ∃ (g g' : ℕ) (w : Fin g → Y) (w' : Fin g' → Y) (Θ : Matrix (Fin g) (Fin g) R)
        (Θ' : Matrix (Fin g) (Fin g') R) (idx : Fin g → ι),
        (g : ℕ∞) = Module.length R (Y ⧸ nnYe (Y := Y) pr e) ∧
        Submodule.span R (Set.range w ∪ Set.range w' : Set Y) = ⊤ ∧
        (∀ k, e • w' k = 0) ∧ (∀ j, εt (idx j) • w j = w j) ∧
        (∀ j, ∑ k, Θ j k • w k + ∑ k, Θ' j k • w' k = 0) ∧
        (∀ j k, pr (Θ' j k) = 0) ∧
        (∀ j k, k < j → (pr (Θ j k)).1 = 0) ∧
        (∀ j, (pr (Θ j j)).1 = 1 - ε (idx j) + (pr (algebraMap O R ϖ)).1 * ε (idx j)) ∧
        (∀ j k, (pr (Θ j k)).2 = if j = k then 1 else 0) ∧
        (blockOf (fun j k => ιO (pr (Θ j k)).1)).det = (algebraMap O K ϖ) ^ g ∧
        (g : ℕ∞) ≤ ∑ i, Module.length O (epsImg O (M := Y ⧸ nnYe (Y := Y) pr e) (εt i))
def StatLemmaFb : Prop :=
  ∀ (O : Type*) (R OO BB Y : Type u) [CommRing O] [IsLocalRing O] [Ring R] [Algebra O R]
    [Module.Finite O R] [Ring OO] [Ring BB] [AddCommGroup Y] [Module R Y] [Module.Finite R Y] [Module O Y] [IsScalarTower O R Y]
    (pr : R →+* OO × BB), Function.Surjective pr →
    (∀ x : R, pr x = 0 → ∀ r : R, IsUnit (1 + r * x)) →
    ∀ ϖ : O, ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ e : R, IsIdempotentElem e → pr e = (1, 0) →
    ∀ (ι : Type) [Fintype ι] (ε : ι → OO) (εt : ι → R), (∀ i, IsIdempotentElem (εt i)) →
      (∀ i, pr (εt i) = (ε i, 0)) → (∀ i, e * εt i * e = εt i) →
      (∀ (S : Type u) [AddCommGroup S] [Module R S], IsSimpleModule R S →
        (∀ x : R, pr x = 0 → ∀ s : S, x • s = 0) → (∀ s : S, e • s = s) →
        ∃ i, ∃ s : S, εt i • s ≠ 0) →
      IsFiniteLength R (Y ⧸ nnY (Y := Y) pr) →
      ∀ (K : Type*) [Field K] [Algebra O K] (N : Type) [Fintype N] [DecidableEq N]
        (ιO : OO →+* Matrix N N K),
        ιO ((pr (algebraMap O R ϖ)).1) = algebraMap O K ϖ • (1 : Matrix N N K) →
      ∃ (g g' : ℕ) (w : Fin g → Y) (w' : Fin g' → Y) (Θ : Matrix (Fin g) (Fin g) R)
        (Θ' : Matrix (Fin g) (Fin g') R) (idx : Fin g → ι),
        (g : ℕ∞) = Module.length R (Y ⧸ nnYe (Y := Y) pr e) ∧
        Submodule.span R (Set.range w ∪ Set.range w' : Set Y) = ⊤ ∧
        (∀ k, e • w' k = 0) ∧ (∀ j, εt (idx j) • w j = w j) ∧
        (∀ j, ∑ k, Θ j k • w k + ∑ k, Θ' j k • w' k = 0) ∧
        (∀ j k, pr (Θ' j k) = 0) ∧
        (∀ j k, k < j → (pr (Θ j k)).1 = 0) ∧
        (∀ j, (pr (Θ j j)).1 = 1 - ε (idx j) + (pr (algebraMap O R ϖ)).1 * ε (idx j)) ∧
        (∀ j k, (pr (Θ j k)).2 = if j = k then 1 else 0) ∧
        (blockOf (fun j k => ιO (pr (Θ j k)).1)).det =
          (algebraMap O K ϖ) ^ (∑ j, (ιO (ε (idx j))).rank) ∧
        (g : ℕ∞) ≤ ∑ i, Module.length O (epsImg O (M := Y ⧸ nnYe (Y := Y) pr e) (εt i))
def StatLemmaFa : Prop :=
  ∀ (R O : Type*) (Y : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Y] [Module R Y] (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (Θ : Matrix g g R) (n : g → Y),
    Submodule.span R (Set.range n) = ⊤ → (∀ i, ∑ j, Θ i j • n j = 0) →
    Module.length O (Y →ₗ[R] LatQ O d ρ) ≤ IsDiscreteValuationRing.addVal O (bigMat ρ Θ).det
end Formalism.NG


