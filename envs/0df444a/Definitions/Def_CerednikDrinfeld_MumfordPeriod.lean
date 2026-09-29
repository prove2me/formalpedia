-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordPeriod
-- name    : CerednikDrinfeld_MumfordPeriod
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4d59af9e-e29e-56f6-a9c8-53176a878cfb
-- title:
--   Quotient graph data and Mumford period data
-- statement:
--   The first half of the module turns a group acting on a graph into a degeneracy datum. A `GraphAction` of a group $G$ on a simple graph $\mathcal{T}$ with vertex type $W$ (carrying a $G$-action) is the propositional assertion that $v \sim w$ implies $g\cdot v \sim g\cdot w$; from it the darts (ordered adjacent pairs) inherit a $G$-action acting on both coordinates, compatibly with dart reversal. Writing `QuotEdge` for the orbit set $G\backslash\mathrm{Dart}(\mathcal{T})$ and `QuotVert` for $G\backslash W$, the width `stabWidth` of a dart orbit is $\#\mathrm{Stab}_G(d)$ for a chosen representative $d$, with the convention that the value is $1$ when that cardinality is $0$ (infinite stabiliser); the order of the stabiliser is constant along an orbit, and the width of the class of $d$ is computed from $\mathrm{Stab}_G(d)$. Then `quotientDegeneracyData` is the `DegeneracyData` with edge level $G\backslash\mathrm{Dart}(\mathcal{T})$, vertex level $G\backslash W$, the two maps sending $[d]$ to the orbits of its origin and terminus, and this width; `quotientReversal` is the involution induced by $d\mapsto\bar d$, and `formalU` is the integer matrix on dart orbits with $(e,e')$ entry $[\,a(e')=b(e)\,]-[\,\overline{e'}=e\,]$.
--
--   The second half fixes a degeneracy datum $D$ on finite levels, fields $K\subseteq L$ and an additive homomorphism $\mathrm{ord}:K^\times\to\mathbb{Z}$. A `PeriodDatum` is a structure carrying a $\mathbb{Z}$-bilinear map $Q$ on the ribbon kernel $Z=\ker a_*\cap\ker b_*$ with values in $K^\times$, together with two of its properties as fields: symmetry, and $\mathrm{ord}\,Q(x,y)=\sum_e w(e)x_ey_e$. `HeckeAdjointable` asserts, for a `HeckeData` $H$ on $D$, that for each prime $\ell$ and each $y\in Z$ some $y'$ satisfies $Q(y, T_\ell z)=Q(y',z)$ for all $z$ — existence of an adjoint, not a formula for it. Composing $Q$ with the map $K^\times\to L^\times$ gives `QL : Z → Hom(Z,L^\times)`; its range is the `periodLattice` $\Lambda$, the quotient $\mathrm{Hom}(Z,L^\times)/\Lambda$ is `JacPoints`, `U` is the submodule of torus points with torsion image, and `π` the induced map $U\to\mathrm{JacPoints}$. Finally `IsTorsionOf T` is a predicate on an abstract abelian group $T$: some additive homomorphism $U\to T$ has torsion image containing all torsion of $T$ and kernel exactly $\Lambda$ — an identification of the torsion of $T$ with $U/\Lambda$ up to abstract isomorphism rather than a chosen one.
--
--   **Relation to Mathlib.** Mathlib supplies `SimpleGraph.Dart`, orbit quotients `orbitRel.Quotient`, stabilisers and `Submodule.torsion`; the class `GraphAction` (adjacency-preserving action, rather than a homomorphism into the graph's automorphism group), the induced action on darts, and all the period-datum notions are the project's own.
--
--   **Where it is used.** These definitions package the combinatorial and multiplicative input of the Čerednik–Drinfeld description of a Shimura curve at a prime of bad reduction: the quotient of the Bruhat–Tits tree by a discrete subgroup gives the dual graph with thicknesses of the special fibre, and a period datum gives the multiplicative period pairing whose valuation is the monodromy pairing, hence the toric description of the Jacobian's points and its torsion. They feed the component-group computations used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean

import Definitions.Def_CerednikDrinfeld_Ribbon
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.BilinearMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section
namespace CerednikDrinfeld
namespace Mumford

open ModularCurve MulAction

class GraphAction (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) : Prop where
  smul_adj : ∀ (g : G) {v w : W}, 𝒯.Adj v w → 𝒯.Adj (g • v) (g • w)

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

instance dartAction : MulAction G 𝒯.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), GraphAction.smul_adj g d.adj⟩
  one_smul d := SimpleGraph.Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d := SimpleGraph.Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))

@[simp] theorem smul_dart_fst (g : G) (d : 𝒯.Dart) : (g • d).fst = g • d.fst := rfl
@[simp] theorem smul_dart_snd (g : G) (d : 𝒯.Dart) : (g • d).snd = g • d.snd := rfl

theorem smul_dart_symm (g : G) (d : 𝒯.Dart) : (g • d).symm = g • d.symm := rfl

abbrev QuotEdge (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

abbrev QuotVert (G : Type) [Group G] (W : Type) [MulAction G W] := orbitRel.Quotient G W

theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

variable (G) in

def stabWidth (e : QuotEdge G 𝒯) : ℕ+ :=
  Nat.toPNat' (Nat.card (stabilizer G e.out))

theorem stabWidth_mk (d : 𝒯.Dart) :
    stabWidth G 𝒯 (Quotient.mk'' d) = Nat.toPNat' (Nat.card (stabilizer G d)) :=
  congrArg Nat.toPNat' (Nat.card_congr
    (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d)).toEquiv)

variable (G) in

def quotientDegeneracyData : DegeneracyData (QuotEdge G 𝒯) (QuotVert G W) where
  a := Quotient.map' (fun d : 𝒯.Dart => d.fst) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  b := Quotient.map' (fun d : 𝒯.Dart => d.snd) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  w := stabWidth G 𝒯

variable (G) in

def quotientReversal : QuotEdge G 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' SimpleGraph.Dart.symm (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)

variable (G) in

def formalU [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [Fintype (QuotVert G W)]
    [DecidableEq (QuotVert G W)] :
    Matrix (QuotEdge G 𝒯) (QuotEdge G 𝒯) ℤ :=
  (degeneracyMatrix (quotientDegeneracyData G 𝒯).b).transpose * degeneracyMatrix (quotientDegeneracyData G 𝒯).a
    - Matrix.of fun e e' => if quotientReversal G 𝒯 e' = e then 1 else 0

structure PeriodDatum {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (K L : Type) [Field K] [Field L] [Algebra K L] (ord : Additive Kˣ →+ ℤ) where

  Q : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive Kˣ

  Q_symm : ∀ x y, Q x y = Q y x

  ord_Q : ∀ x y, ord (Q x y) = ribbonGram D x y

def PeriodDatum.HeckeAdjointable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)
    (H : HeckeData D) : Prop :=
  ∀ (ℓ : Nat.Primes) (y : ↥(ribbonKernel D)), ∃ y' : ↥(ribbonKernel D),
    ∀ z : ↥(ribbonKernel D), P.Q y (heckeKernelMap H ℓ z) = P.Q y' z

def unitsBaseChange (K L : Type) [Field K] [Field L] [Algebra K L] : Additive Kˣ →ₗ[ℤ] Additive Lˣ :=
  (MonoidHom.toAdditive (Units.map (algebraMap K L).toMonoidHom)).toIntLinearMap

@[simp] theorem unitsBaseChange_apply (K L : Type) [Field K] [Field L] [Algebra K L] (u : Kˣ) :
    unitsBaseChange K L (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u) := rfl

namespace PeriodDatum
variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

set_option linter.unusedVariables false in

abbrev TorusPoints (P : PeriodDatum D K L ord) : Type := ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ

def QL : ↥(ribbonKernel D) →ₗ[ℤ] P.TorusPoints := P.Q.compr₂ (unitsBaseChange K L)

@[simp] theorem QL_apply (x y : ↥(ribbonKernel D)) : P.QL x y = unitsBaseChange K L (P.Q x y) := rfl

def periodLattice : Submodule ℤ P.TorusPoints := LinearMap.range P.QL

abbrev JacPoints : Type := P.TorusPoints ⧸ P.periodLattice

def U : Submodule ℤ P.TorusPoints := (Submodule.torsion ℤ P.JacPoints).comap P.periodLattice.mkQ

def π : ↥P.U →ₗ[ℤ] P.JacPoints := P.periodLattice.mkQ ∘ₗ P.U.subtype

def IsTorsionOf (T : Type) [AddCommGroup T] : Prop :=
  ∃ e : ↥P.U →+ T, (∀ t : T, IsOfFinAddOrder t → t ∈ e.range) ∧ (∀ u, IsOfFinAddOrder (e u)) ∧
    ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice
end PeriodDatum

end Mumford
end CerednikDrinfeld
end


