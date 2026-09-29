-- Prove2me | Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
-- name    : CerednikDrinfeld_SchottkyTreeAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/169f7ea7-f9f3-5942-b867-166c389a78ac
-- title:
--   Tree lattices, Schottky actions, and quotient-graph cycle classes
-- statement:
--   Throughout, a group $G$ acts on a type $W$ carrying a simple graph $\mathcal T$, the action preserving adjacency (`GraphAction`), so that $G$ acts on the darts $\mathcal T.\mathrm{Dart}$ (ordered adjacent pairs) with $g\cdot(v,w)=(g\cdot v,g\cdot w)$; `QuotVert G W` and `QuotEdge G 𝒯` are the orbit quotients of $W$ and of the dart set. Two predicates, each a structure whose fields are the defining conditions, are introduced. `IsTreeLattice G 𝒯` asserts: the action on $W$ is faithful; every vertex stabiliser $\mathrm{Stab}_G(w)$ is finite; and both orbit quotients $G\backslash W$ and $G\backslash\mathrm{Dart}(\mathcal T)$ are finite. `IsSchottky G 𝒯` asserts: every vertex stabiliser is trivial; no group element inverts a dart, i.e. $g\cdot d\neq \bar d$ for all $g$ and $d$; and again both orbit quotients are finite. Under `IsSchottky` the dart stabilisers are trivial, the widths `stabWidth G 𝒯` of all dart orbits equal $1$ (hence the $w$-component of `quotientDegeneracyData G 𝒯` is constantly $1$), and, when $W$ is non-empty, `IsSchottky` implies `IsTreeLattice`; from `IsTreeLattice` one extracts `Fintype` structures on the two orbit quotients.
--
--   The second half defines a cycle map. For a dart orbit $q$, `dartIndex 𝒯 q d` is $1$ if $[d]=q$, $-1$ if $[\bar d]=q$, and is the difference of the two indicator values in general. Given a family $\mathrm{orb}\colon E\to G\backslash\mathrm{Dart}(\mathcal T)$ of dart orbits, `walkCycle 𝒯 orb p` is a map $E \to \mathbb Z$ sending $e$ to the sum of `dartIndex 𝒯 (orb e)` over the darts of a walk $p$ in $\mathcal T$; it vanishes on the trivial walk, is additive on concatenation, changes sign under reversal, is unchanged when the walk is transported by the graph homomorphism `smulHom g` induced by an element $g$, and satisfies the corresponding dart-level identities. `pathCycle 𝒯 orb v₀ g` is `walkCycle` evaluated on a path from $v_0$ to $g\cdot v_0$ chosen by `somePath` from a reachability witness, and is $0$ when $g\cdot v_0$ is not reachable from $v_0$; if $\mathcal T$ is acyclic it agrees with `walkCycle` of any path from $v_0$ to $g\cdot v_0$, by uniqueness of paths. Finally `ActsThrough W ρ`, for a homomorphism $\rho\colon G\to H$ with both groups acting on $W$, asserts $g\cdot w=\rho(g)\cdot w$ for all $g$ and $w$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — simple graphs, darts, walks and paths, acyclicity, group actions, stabilisers, `FaithfulSMul`, and orbit quotients — but has no notion of a tree lattice, of a Schottky action on a graph, or of the dart-index cycle class of a walk; these, like the `GraphAction` class and the quotient degeneracy datum they refer to, are the project's own.
--
--   **Where it is used.** These predicates isolate the group-theoretic input for the Mumford–Čerednik–Drinfeld description of the $r$-adic uniformisation used at the auxiliary prime: applied to the Bruhat–Tits tree with its $\mathrm{PGL}_2$-action, a tree lattice yields a finite quotient graph whose degeneracy datum, widths and ribbon kernel carry the character lattice, period pairing and component group data, while the Schottky case is the one with trivial stabilisers and all widths $1$. The cycle map `pathCycle` attaches to each group element a class in the integral cycles of the quotient graph, the mechanism by which the abelianisation of the acting group is matched with the homology of that graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_SchottkyTreeAction.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Algebra.Group.Action.Faithful

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

variable (G) in

structure IsTreeLattice : Prop where

  faithful : FaithfulSMul G W

  finite_stabilizer : ∀ w : W, Finite (stabilizer G w)

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)

variable (G) in

structure IsSchottky : Prop where

  stabilizer_eq_bot : ∀ w : W, stabilizer G w = ⊥

  smul_ne_symm : ∀ (g : G) (d : 𝒯.Dart), g • d ≠ d.symm

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)

theorem stabilizer_dart_le (d : 𝒯.Dart) : stabilizer G d ≤ stabilizer G d.fst := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← smul_dart_fst 𝒯 g d, hg]

namespace IsSchottky

variable {𝒯}

theorem stabilizer_dart_eq_bot (h : IsSchottky G 𝒯) (d : 𝒯.Dart) : stabilizer G d = ⊥ :=
  le_bot_iff.mp ((stabilizer_dart_le 𝒯 d).trans (h.stabilizer_eq_bot d.fst).le)

theorem stabWidth_eq_one (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) : stabWidth G 𝒯 e = 1 := by
  induction e using Quotient.inductionOn' with
  | h d => rw [stabWidth_mk, h.stabilizer_dart_eq_bot d, Subgroup.card_bot]; rfl

theorem quotientDegeneracyData_w (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) : (quotientDegeneracyData G 𝒯).w e = 1 :=
  h.stabWidth_eq_one e

theorem isTreeLattice [Nonempty W] (h : IsSchottky G 𝒯) : IsTreeLattice G 𝒯 where
  faithful := ⟨fun {g₁ g₂} hg => by
    obtain ⟨w⟩ := ‹Nonempty W›
    have : g₂⁻¹ * g₁ ∈ stabilizer G w := by rw [mem_stabilizer_iff, mul_smul, hg w, inv_smul_smul]
    rw [h.stabilizer_eq_bot w, Subgroup.mem_bot] at this
    exact (eq_of_inv_mul_eq_one this).symm⟩
  finite_stabilizer w := by rw [h.stabilizer_eq_bot w]; infer_instance
  finite_quotVert := h.finite_quotVert
  finite_quotEdge := h.finite_quotEdge

end IsSchottky

namespace IsTreeLattice

variable {𝒯}

@[reducible] def fintypeQuotVert (h : IsTreeLattice G 𝒯) : Fintype (QuotVert G W) :=
  @Fintype.ofFinite _ h.finite_quotVert

@[reducible] def fintypeQuotEdge (h : IsTreeLattice G 𝒯) : Fintype (QuotEdge G 𝒯) :=
  @Fintype.ofFinite _ h.finite_quotEdge

end IsTreeLattice

def ActsThrough (W : Type) {G H : Type} [Group G] [Group H] [MulAction G W] [MulAction H W] (ρ : G →* H) : Prop :=
  ∀ (g : G) (w : W), g • w = ρ g • w

variable {𝒯} in

def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun w := g • w
  map_rel' h := GraphAction.smul_adj g h

@[simp] theorem smulHom_apply (g : G) (w : W) : smulHom (𝒯 := 𝒯) g w = g • w := rfl

@[simp] theorem smulHom_mapDart (g : G) (d : 𝒯.Dart) : (smulHom g).mapDart d = g • d := rfl

theorem quotEdge_mk_smul (g : G) (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) (g • d) : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d :=
  Quotient.sound (mem_orbit d g)

def dartIndex [DecidableEq (QuotEdge G 𝒯)] (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : ℤ :=
  (if Quotient.mk (orbitRel G 𝒯.Dart) d = q then 1 else 0) -
    (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = q then 1 else 0)

def walkCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) {u v : W} (p : 𝒯.Walk u v) :
    E → ℤ :=
  fun e => (p.darts.map (dartIndex 𝒯 (orb e))).sum

variable {𝒯} in

def somePath {u v : W} (h : 𝒯.Reachable u v) : 𝒯.Path u v := by
  classical exact h.some.toPath

open scoped Classical in

def pathCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W) (g : G) : E → ℤ :=
  if h : 𝒯.Reachable v₀ (g • v₀) then walkCycle 𝒯 orb (somePath h : 𝒯.Walk v₀ (g • v₀)) else 0

section lemmas

variable [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)

theorem dartIndex_symm (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : dartIndex 𝒯 q d.symm = -dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, SimpleGraph.Dart.symm_symm]; ring

theorem dartIndex_smul (q : QuotEdge G 𝒯) (g : G) (d : 𝒯.Dart) : dartIndex 𝒯 q (g • d) = dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, smul_dart_symm, quotEdge_mk_smul, quotEdge_mk_smul]

@[simp] theorem walkCycle_nil (u : W) : walkCycle 𝒯 orb (SimpleGraph.Walk.nil : 𝒯.Walk u u) = 0 := by
  funext e; simp [walkCycle]

theorem walkCycle_cons {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) (e : E) :
    walkCycle 𝒯 orb (SimpleGraph.Walk.cons h p) e = dartIndex 𝒯 (orb e) ⟨(u, v), h⟩ + walkCycle 𝒯 orb p e := by
  simp [walkCycle]

theorem walkCycle_append {u v w : W} (p : 𝒯.Walk u v) (q : 𝒯.Walk v w) :
    walkCycle 𝒯 orb (p.append q) = walkCycle 𝒯 orb p + walkCycle 𝒯 orb q := by
  funext e; simp [walkCycle, SimpleGraph.Walk.darts_append, List.sum_append]

theorem walkCycle_reverse {u v : W} (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb p.reverse = -walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map,
    Pi.neg_apply]
  induction p.darts with
  | nil => simp
  | cons d l ih => simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, dartIndex_symm]; ring

theorem walkCycle_map_smulHom {u v : W} (g : G) (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb (p.map (smulHom g)) = walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  exact List.map_congr_left fun d _ => by rw [Function.comp_apply, smulHom_mapDart, dartIndex_smul]

theorem pathCycle_eq_walkCycle (hac : 𝒯.IsAcyclic) (v₀ : W) (g : G) (p : 𝒯.Path v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = walkCycle 𝒯 orb (p : 𝒯.Walk v₀ (g • v₀)) := by
  rw [pathCycle, dif_pos p.1.reachable, hac.path_unique (somePath p.1.reachable) p]

theorem pathCycle_of_not_reachable (v₀ : W) (g : G) (h : ¬𝒯.Reachable v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = 0 := by
  rw [pathCycle, dif_neg h]

end lemmas

end Mumford
end CerednikDrinfeld

end


