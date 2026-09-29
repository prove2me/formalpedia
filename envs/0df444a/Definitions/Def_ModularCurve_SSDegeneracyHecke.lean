-- Prove2me | Definitions.Def_ModularCurve_SSDegeneracyHecke
-- name    : ModularCurve_SSDegeneracyHecke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/9640a586-2b47-50ca-b555-b686d01e5208
-- title:
--   Supersingular degeneracy legs, Hecke matrices, level datum
-- statement:
--   Throughout, $F_N$ denotes `modularFunctionFieldC K N`, the subfield $K(j(q),j(q^N))$ of the Laurent series over $K$, and $\Sigma(N)$ denotes `ssPlaces p N K`, the places of $F_N$ that are rational, affine for the pair of generators, and whose value at $j(q)$ lies in `ssJSet p K`. The first group of declarations builds the two degeneracy legs between levels: if $j(q^M)\in F_{Ms}$ then $F_M\le F_{Ms}$ and `levelAlphaC` is the resulting inclusion of $K$-algebras; if $j(q^s)\in F_{Ms}$ then the substitution $q\mapsto q^s$ carries $F_M$ into $F_{Ms}$ (because it sends $j(q^M)$ to $j(q^{Ms})$) and `levelBetaC` is the resulting $K$-algebra map, with the two coercion lemmas identifying their effect on Laurent series. `IsAtkinLehnerLevelAut` is the predicate on a $K$-algebra automorphism $\sigma$ of $F_{Ms}$ that $\sigma$ interchanges $j(q)$ with $j(q^s)$ and $j(q^{Ms})$ with $j(q^M)$; `autOnPlaces` is the induced bijection of places.
--
--   Next, two integral matrices indexed by $\Sigma(N)\times\Sigma(N)$. Given integrality of the two legs $F_N\to K(j(q),j(q^N),j(q^{\ell}),j(q^{N\ell}))$, the entry $(y,x)$ of `ssHeckeMatrixC` is the sum, over all places $W$ of the roof field restricting to $x$ along $\beta$ and to $y$ along $\alpha$, of the ramification index of $W$ along $\beta$ times the inertia degree along $\alpha$. The entry $(y,x)$ of `ssFrobMatrixC` is $1$ when $y$ is the Frobenius image of $x$ and $0$ otherwise. `ssHeckeFamilyC` assembles these over primes $\ell$, using the Frobenius matrix when $\ell=p$.
--
--   `SSLevelDatum p K M s` is a structure packaging: the two memberships above; integrality of `levelAlphaC`, `levelBetaC` and of all level-$N$ Hecke legs; that both restrictions of a place in $\Sigma(Ms)$ lie in $\Sigma(M)$; an automorphism satisfying `IsAtkinLehnerLevelAut` preserving $\Sigma(Ms)$; and a `ModularPolynomialData p` with its Kronecker congruence. From such a datum $X$ come the maps `fst`, `snd` : $\Sigma(Ms)\to\Sigma(M)$, the self-map `atkinLehnerPerm` of $\Sigma(Ms)$, the degeneracy datum with these two maps and width $\max(1,\mathrm{placeWidth})$, and the two Hecke families `edgeHecke`, `vertexHecke`. `HeckeLaws` is the conjunction: both families commute among themselves; for every prime $\ell\neq s$ each of the two pushforwards intertwines `edgeHecke` with `vertexHecke`; and the joint kernel of the two pushforwards is stable under every `edgeHecke` matrix. `heckeData` returns the corresponding [`CerednikDrinfeld.HeckeData`](../def/CerednikDrinfeld_Ribbon.html#L94) with bad set $\{s\}$ when `HeckeLaws` holds, and the zero family otherwise.
--
--   **Relation to Mathlib.** Mathlib supplies the intermediate-field, Laurent series and integer-matrix infrastructure used here; the modular function fields, their places and supersingular loci, the degeneracy legs and the degeneracy/Hecke data structures are the project's own notions.
--
--   **Where it is used.** The degeneracy datum and Hecke data produced here are the combinatorial input to the ribbon construction: edges are the supersingular places at level $Ms$, vertices those at level $M$, with the two degeneracy maps and the widths of the places, and a commuting family of Hecke matrices compatible with the pushforwards away from $s$. This is the shape in which the component group of the special fibre, with its Hecke action, enters the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SSDegeneracyHecke.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section LevelLegs

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

theorem modularFunctionFieldC_le_of_mem (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M ≤ modularFunctionFieldC K (M * s) := by
  show IntermediateField.adjoin K {jqModC K, jqNModC K M} ≤ _
  refine IntermediateField.adjoin_le_iff.mpr ?_
  intro x hx
  rcases hx with h | h
  · subst h
    exact jqModC_mem K (M * s)
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact hM

theorem map_qExpandAlgC_le_of_mem (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    (modularFunctionFieldC K M).map (qExpandAlgC K s) ≤ modularFunctionFieldC K (M * s) := by
  show (IntermediateField.adjoin K {jqModC K, jqNModC K M}).map (qExpandAlgC K s) ≤ _
  rw [IntermediateField.adjoin_map]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, qExpandAlgC_apply] at hx
  rcases hx with h | h
  · subst h
    exact hS
  · rw [Set.mem_singleton_iff] at h
    subst h
    show qExpand K s (jqNModC K M) ∈ modularFunctionFieldC K (M * s)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm s M]
    exact jqNModC_mem K (M * s)

def levelAlphaC (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →ₐ[K] modularFunctionFieldC K (M * s) :=
  IntermediateField.inclusion (modularFunctionFieldC_le_of_mem K M s hM)

@[simp]
theorem coe_levelAlphaC (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldC K M) :
    (levelAlphaC K M s hM x : LaurentSeries K) = (x : LaurentSeries K) :=
  IntermediateField.coe_inclusion _ x

def levelBetaCRingHom (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →+* modularFunctionFieldC K (M * s) where
  toFun x := ⟨qExpand K s (x : LaurentSeries K), map_qExpandAlgC_le_of_mem K M s hS ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand K s))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K s) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K s))
  map_add' _ _ := Subtype.ext (map_add (qExpand K s) _ _)

def levelBetaC (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →ₐ[K] modularFunctionFieldC K (M * s) :=
  { levelBetaCRingHom K M s hS with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K s (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_levelBetaC (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldC K M) :
    (levelBetaC K M s hS x : LaurentSeries K) = qExpand K s (x : LaurentSeries K) :=
  rfl

def IsAtkinLehnerLevelAut (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s))
    (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s))
    (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)) : Prop :=
  σ (jGeomGen K (M * s)) = ⟨jqNModC K s, hS⟩ ∧ σ ⟨jqNModC K s, hS⟩ = jGeomGen K (M * s) ∧
    σ (jNGeomGen K (M * s)) = ⟨jqNModC K M, hM⟩ ∧ σ ⟨jqNModC K M, hM⟩ = jNGeomGen K (M * s)

def autOnPlaces (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)) :
    Place K (modularFunctionFieldC K (M * s)) ≃ Place K (modularFunctionFieldC K (M * s)) :=
  Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c)

end LevelLegs

section Matrices

variable (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

open Classical in

def ssHeckeMatrixC (ℓ : ℕ) [NeZero ℓ] (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral)
    (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral) : Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  Matrix.of fun y x =>
    ∑ᶠ W : Place K (charLDegeneracyRoof K N ℓ),
      if Place.restrictAlong (heckeBetaC K N ℓ) hβ W = x.1 ∧ Place.restrictAlong (heckeAlphaC K N ℓ) hα W = y.1 then
        (Place.ramificationIndexAlong (heckeBetaC K N ℓ) W : ℤ) * (Place.inertiaDegAlong (heckeAlphaC K N ℓ) hα W : ℤ)
      else 0

variable [Fact p.Prime] [CharP K p]

open Classical in

def ssFrobMatrixC (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data) :
    Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  Matrix.of fun y x => if frobOnPlacesGeomLevel K N data hKr x.1 = y.1 then 1 else 0

def ssHeckeFamilyC (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) : Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
  if (ℓ : ℕ) = p then ssFrobMatrixC p K N data hKr else ssHeckeMatrixC p K N ℓ (hlegs ℓ).1 (hlegs ℓ).2

end Matrices

section Datum

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]

structure SSLevelDatum where

  mem_M : jqNModC K M ∈ modularFunctionFieldC K (M * s)

  mem_s : jqNModC K s ∈ modularFunctionFieldC K (M * s)

  fstIntegral : (levelAlphaC K M s mem_M).toRingHom.IsIntegral

  sndIntegral : (levelBetaC K M s mem_s).toRingHom.IsIntegral

  legsIntegral : ∀ (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ],
    (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral

  fst_mem : ∀ W, W ∈ ssPlaces p (M * s) K →
    Place.restrictAlong (levelAlphaC K M s mem_M) fstIntegral W ∈ ssPlaces p M K

  snd_mem : ∀ W, W ∈ ssPlaces p (M * s) K →
    Place.restrictAlong (levelBetaC K M s mem_s) sndIntegral W ∈ ssPlaces p M K

  atkinLehnerAut : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)
  isAtkinLehner : IsAtkinLehnerLevelAut K M s mem_M mem_s atkinLehnerAut

  stable : ∀ W, W ∈ ssPlaces p (M * s) K → autOnPlaces K M s atkinLehnerAut W ∈ ssPlaces p (M * s) K

  frobData : ModularPolynomialData p

  kronecker : KroneckerCongruence p frobData

namespace SSLevelDatum

variable {p K M s}
variable (X : SSLevelDatum p K M s)

def fst (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p M K) :=
  ⟨Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral W.1, X.fst_mem W.1 W.2⟩

def snd (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p M K) :=
  ⟨Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral W.1, X.snd_mem W.1 W.2⟩

def atkinLehnerPerm (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p (M * s) K) :=
  ⟨autOnPlaces K M s X.atkinLehnerAut W.1, X.stable W.1 W.2⟩

def degeneracyData : CerednikDrinfeld.DegeneracyData ↥(ssPlaces p (M * s) K) ↥(ssPlaces p M K) where
  a := X.fst
  b := X.snd
  w W := Nat.toPNat' (placeWidth (M * s) W.1)

def edgeHecke : Nat.Primes → Matrix ↥(ssPlaces p (M * s) K) ↥(ssPlaces p (M * s) K) ℤ :=
  ssHeckeFamilyC p K (M * s) X.frobData X.kronecker (X.legsIntegral (M * s))

def vertexHecke : Nat.Primes → Matrix ↥(ssPlaces p M K) ↥(ssPlaces p M K) ℤ :=
  ssHeckeFamilyC p K M X.frobData X.kronecker (X.legsIntegral M)

section Laws

variable [Fact s.Prime] [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]

def HeckeLaws : Prop :=
  (∀ ℓ ℓ' : Nat.Primes, Commute (X.edgeHecke ℓ) (X.edgeHecke ℓ')) ∧
  (∀ ℓ ℓ' : Nat.Primes, Commute (X.vertexHecke ℓ) (X.vertexHecke ℓ')) ∧
  (∀ ℓ : Nat.Primes, ℓ ∉ ({⟨s, Fact.out⟩} : Finset Nat.Primes) → ∀ i : Fin 2,
    ∀ x : ↥(ssPlaces p (M * s) K) → ℤ,
      CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) =
        (X.vertexHecke ℓ).mulVecLin (CerednikDrinfeld.jointDelta X.degeneracyData i x)) ∧
  (∀ ℓ : Nat.Primes, ∀ x : ↥(ssPlaces p (M * s) K) → ℤ,
    (∀ i, CerednikDrinfeld.jointDelta X.degeneracyData i x = 0) →
      ∀ i, CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) = 0)

open Classical in

def heckeData : CerednikDrinfeld.HeckeData X.degeneracyData :=
  if h : X.HeckeLaws then
    { T := X.edgeHecke
      Tv := X.vertexHecke
      comm := h.1
      commv := h.2.1
      S := {⟨s, Fact.out⟩}
      good_equivariant := h.2.2.1
      kernel_stable := h.2.2.2 }
  else
    { T := 0
      Tv := 0
      comm := fun _ _ => Commute.refl 0
      commv := fun _ _ => Commute.refl 0
      S := {⟨s, Fact.out⟩}
      good_equivariant := fun _ _ i x => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
      kernel_stable := fun _ x _ i => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero] }

end Laws

end SSLevelDatum

end Datum

end ModularCurve

end


