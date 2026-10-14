-- Prove2me | Definitions.Def_SelmerGroup_ContinuousH1
-- name    : SelmerGroup_ContinuousH1
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T15:52:35.265855+00:00
-- url     : https://prove2.me/theorems/a71cf60d-9ca5-4e54-bb21-4f080a1fd56a
-- title:
--   Continuous $H^1$ with discrete coefficients
-- statement:
--   Let $G$ be a topological group acting additively on an abelian group $M$ through a homomorphism $\rho: G\to\mathrm{End}(M)$; $M$ carries the discrete topology.
--
--   1. A **continuous 1-cocycle** is a locally constant map $c:G\to M$ with $c(gh)=c(g)+\rho(g)\,c(h)$ for all $g,h\in G$. These form a subgroup $Z^1(G,M)$ of $M^G$.
--   2. A **1-coboundary** is a map $g\mapsto\rho(g)m-m$ for some $m\in M$; these form a subgroup $B^1(G,M)$.
--   3. The **continuous first cohomology group** is
--   $$H^1(G,M)=Z^1(G,M)\,/\,(Z^1(G,M)\cap B^1(G,M)).$$
--   4. An equivariant homomorphism $\alpha:M\to N$ (i.e. $\alpha(\rho(g)m)=\sigma(g)\alpha(m)$) induces $\alpha_*:H^1(G,M)\to H^1(G,N)$, $[c]\mapsto[\alpha\circ c]$.
--
--   This is the Galois cohomology used for the Selmer and Tate–Shafarevich groups, where $G$ is a profinite Galois group and $M$ a discrete Galois module.
--
--   **Formalization Note** Continuity into a discrete module is expressed as `IsLocallyConstant`. Coboundaries are intersected with the continuous cocycles; for discrete modules (open stabilisers) every coboundary is continuous anyway.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib

/-!
# Continuous first cohomology with discrete coefficients

For a topological group `G` acting additively on an abelian group `M` (through
`ρ : G →* AddMonoid.End M`), with `M` regarded as a *discrete* module, we define
* the continuous 1-cocycles: locally constant maps `c : G → M` with
  `c (g * h) = c g + ρ g (c h)`;
* the 1-coboundaries `g ↦ ρ g m - m`;
* `H1 ρ`, continuous 1-cocycles modulo 1-coboundaries;
* the map `H1.map` induced by an equivariant homomorphism of coefficient modules.
-/

noncomputable section

namespace SelmerGroup

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M]
variable {N : Type*} [AddCommGroup N]

/-- Continuous (= locally constant, since `M` is discrete) inhomogeneous 1-cocycles. -/
def cocycles (ρ : G →* AddMonoid.End M) : AddSubgroup (G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h : G, c (g * h) = c g + ρ g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add]
    abel
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨ha.neg, fun g h => ?_⟩
    simp only [Pi.neg_apply, ha', map_neg]
    abel

/-- The coboundary map `m ↦ (g ↦ ρ g m - m)`. -/
def coboundaryHom (ρ : G →* AddMonoid.End M) : M →+ (G → M) where
  toFun m := fun g => ρ g m - m
  map_zero' := by ext g; simp
  map_add' m m' := by ext g; simp only [map_add, Pi.add_apply]; abel

/-- The 1-coboundaries, viewed inside the group of continuous 1-cocycles. -/
def coboundaries (ρ : G →* AddMonoid.End M) : AddSubgroup (cocycles ρ) :=
  (coboundaryHom ρ).range.addSubgroupOf (cocycles ρ)

/-- Continuous first cohomology `H¹(G, M)` of the discrete module `M`. -/
def H1 (ρ : G →* AddMonoid.End M) : Type _ := cocycles ρ ⧸ coboundaries ρ

instance (ρ : G →* AddMonoid.End M) : AddCommGroup (H1 ρ) :=
  inferInstanceAs (AddCommGroup (cocycles ρ ⧸ coboundaries ρ))

/-- The cohomology class of a continuous 1-cocycle. -/
def H1.mk (ρ : G →* AddMonoid.End M) : cocycles ρ →+ H1 ρ :=
  QuotientAddGroup.mk' (coboundaries ρ)

/-- Post-composition of continuous cocycles with an equivariant homomorphism. -/
def cocyclesMap (ρ : G →* AddMonoid.End M) (σ : G →* AddMonoid.End N) (α : M →+ N)
    (hα : ∀ g m, α (ρ g m) = σ g (α m)) : cocycles ρ →+ cocycles σ where
  toFun c := ⟨fun g => α (c.1 g), c.2.1.comp α, fun g h => by
    simp only [c.2.2 g h, map_add, hα]⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- The map `H¹(G, M) → H¹(G, N)` induced by an equivariant homomorphism `α : M → N`. -/
def H1.map (ρ : G →* AddMonoid.End M) (σ : G →* AddMonoid.End N) (α : M →+ N)
    (hα : ∀ g m, α (ρ g m) = σ g (α m)) : H1 ρ →+ H1 σ :=
  QuotientAddGroup.map (coboundaries ρ) (coboundaries σ) (cocyclesMap ρ σ α hα) (by
    rintro c ⟨m, hm⟩
    refine ⟨α m, ?_⟩
    funext g
    have := congrFun hm g
    simp only [coboundaryHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
    change σ g (α m) - α m = α (c.1 g)
    rw [← hα, ← map_sub]
    exact congrArg α this)

end SelmerGroup


