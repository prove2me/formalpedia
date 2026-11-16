-- Prove2me | Definitions.Def_CoDecompFO_Supplement_StratTotal
-- name    : CoDecompFO_Supplement_StratTotal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:34.892196+00:00
-- url     : https://prove2.me/theorems/80f0558b-24fa-4bcf-b0b0-104f6da84f0c
-- title:
--   Families, diagrammatic $m$-strategies $\mathrm{Strat}_m(G,\beta)$, projections $f_*$ and the total category $\mathrm{Strat}^\sigma_m$
-- statement:
--   1. **Families** (¶5.24–5.25). An $S$-indexed family in a category $\mathcal C$ is a set $S$ with an object $F_s$ for each $s\in S$; $S=\emptyset$ is allowed and repeated entries are not identified.
--
--   2. **Diagrammatic strategies** (¶5.33, Eq. (3)). $\mathrm{Strat}_0(G,\beta)=\mathbf 1$ and
--   $$\mathrm{Strat}_m(G,\beta)=\prod_{x\in G}\mathrm{Fam}\Big(\sum_{y\in G}\mathrm{Strat}_{m-1}(G,\beta\cdot x\cdot y)\Big):$$
--   for each move $x$ of the universal player, a family of responses $(y,A')$, each a point $y$ with an $(m-1)$-strategy.
--
--   3. **Projection** (Prop. 5.44, Example 5.45, proof of Lemma 5.56). For $f:G\to H$, $(f_*A)(x')$ is the concatenation over $x\in f^{-1}(x')$ of the families $A(x)$, each response $(y,A')$ sent to $(f(y),f_*A')$; a point with empty preimage gets the empty family, and distinct responses with the same image stay distinct.
--
--   4. **Total category** (¶5.50). Objects are triples $(G,\beta,A)$ with $A\in\mathrm{Strat}_m(G,\beta)$; a morphism $(f,\eta):(G,\beta,A)\to(H,\gamma,B)$ is a morphism of positions $f$ with $\eta:f_*A\to B$ in $\mathrm{Strat}_m(H,\gamma)$; composition is $(g,\theta)\circ(f,\eta)=(gf,\theta\circ g_*(\eta))$. The projection functor $p:\mathrm{Strat}^\sigma_m\to\mathrm{Pos}^\sigma_m$ forgets $A$.
--
--   Also defined: the morphism $(f,\mathrm{id}):(G,\beta,A)\to(H,f\beta,f_*A)$ and the coherence isomorphism $g_*(f_*A)\cong h_*A$ for $h=g\circ f$.
--
--   **Formalization Note** Since $f_*A(x')$ is a concatenation, a morphism $\eta:f_*A\to B$ is the same as, for each $x\in G$, an index map from the responses of $A(x)$ to those of $B(f(x))$ and, for each response $(y,A')$ sent to $(y',B')$, the equation $f(y)=y'$ with a morphism $f_*A'\to B'$ one level down. The Lean hom-sets (`StratHom`) are this data, so the total category is the Grothendieck construction of footnote 11 with the coherence isomorphisms built in, and its category laws hold exactly. $\mathrm{Strat}_m(G,\beta)$ does not depend on $\beta$, so the object type is indexed by $G$ and $m$.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶5.24–5.25, p.22; ¶5.33 (Eq. 3), p.23; Prop. 5.44 and Example 5.45, pp.26–27; ¶5.48–5.50 and footnote 11, pp.27–28; proof of Lemma 5.56 (Eq. 8–10), p.31 (PDF pp.24–33)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_Positions

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory

/-- An **`S`-indexed family** in `C` (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, ¶5.24–5.25,
p.22): a diagram `S* → C` out of the discrete category on a set `S`, i.e. a set `S` and an object `F s` for each
`s ∈ S`. "We allow S = ∅, so that Fam(C) contains the empty family." Entries may repeat (Example 5.45: "repeated
entries are not identified"). -/
structure Fam (C : Type 1) : Type 1 where
  /-- The indexing set `S`. -/
  idx : Type
  /-- The entries `F s`. -/
  obj : idx → C

/-- The objects of the category `Strat_m(G, β)` of **diagrammatic `m`-strategies** (¶5.33, Eq. (3), p.23):
`Strat_0(G, β) := 1` and `Strat_m(G, β) := ∏_{x∈G} Fam(∑_{y∈G} Strat_{m−1}(G, β·x·y))`. An object of
`∑_{y∈G} Strat_{m−1}(G, β·x·y)` is a pair `(y, A)`.

**Formalization Note** The category `Strat_m(G, β)` does not depend on `β` (its base case is the terminal category
`1` for every `β`), so the object type is indexed by `G` and `m` only. -/
def StratObj (G : Type) : ℕ → Type 1
  | 0 => PUnit
  | m + 1 => G → Fam (G × StratObj G m)

/-- **Morphisms over a map `f : G → H`** between strategies, `StratHom f m A B`: this is the set of morphisms
`η : f_* A → B` in `Strat_m(H, fβ)`, where `f_*` is the projection functor of Proposition 5.44 (p.26) and of the
proof of Lemma 5.56 (Eq. (8)–(10), p.31), written out with the universal property of the concatenation of families.

At level `m + 1`, `(f_* A)(x')` is the concatenation over `x ∈ f⁻¹(x')` of the families `Fam(T_x)(A(x))`, where
`T_x(y, A') = (f(y), f_* A')`; a morphism of families out of a concatenation is a family of morphisms out of each
summand, and a morphism `(f(y), f_* A') → (y', B')` in the coproduct category `∑_{y'∈H}` exists only when
`f(y) = y'` and is then a morphism `f_* A' → B'` one level down. So a morphism over `f` is, for each `x ∈ G`, an
index map `u` from the responses of `A(x)` to those of `B(f x)` and, for each response `s`, a proof that the
response points correspond under `f` and a morphism over `f` one level down. At level `0` it is the unique
morphism of `1`. -/
def StratHom {G H : Type} (f : G → H) : (m : ℕ) → StratObj G m → StratObj H m → Type
  | 0, _, _ => PUnit
  | m + 1, A, B => (x : G) → Σ u : (A x).idx → (B (f x)).idx, (s : (A x).idx) →
      PLift (f ((A x).obj s).1 = ((B (f x)).obj (u s)).1) ×
        StratHom f m ((A x).obj s).2 ((B (f x)).obj (u s)).2

/-- The identity morphism over `id`. -/
def StratHom.id {G : Type} : (m : ℕ) → (A : StratObj G m) → StratHom (fun x : G => x) m A A
  | 0, _ => PUnit.unit
  | m + 1, A => fun x => ⟨fun s => s, fun s => ⟨⟨rfl⟩, StratHom.id m ((A x).obj s).2⟩⟩

/-- Composition of morphisms over `f` and over `g`, a morphism over `g ∘ f` (¶5.50, p.28: "(g, θ) ∘ (f, η) :=
(gf, θ ∘ g_*(η))", with the coherence isomorphism `(gf)_* ≅ g_* f_*` built in). -/
def StratHom.comp {G H K : Type} {f : G → H} {g : H → K} :
    (m : ℕ) → {A : StratObj G m} → {B : StratObj H m} → {C : StratObj K m} →
      StratHom f m A B → StratHom g m B C → StratHom (g ∘ f) m A C
  | 0, _, _, _, _, _ => PUnit.unit
  | m + 1, _, _, _, η, θ => fun x =>
      ⟨fun s => (θ (f x)).1 ((η x).1 s), fun s =>
        ⟨⟨(congrArg g ((η x).2 s).1.down).trans ((θ (f x)).2 ((η x).1 s)).1.down⟩,
          StratHom.comp m ((η x).2 s).2 ((θ (f x)).2 ((η x).1 s)).2⟩⟩

theorem StratHom.id_comp {G H : Type} {f : G → H} :
    (m : ℕ) → {A : StratObj G m} → {B : StratObj H m} → (η : StratHom f m A B) →
      StratHom.comp m (StratHom.id m A) η = η
  | 0, _, _, _ => rfl
  | m + 1, _, _, η => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun s =>
      Prod.ext rfl (StratHom.id_comp m ((η x).2 s).2)))

theorem StratHom.comp_id {G H : Type} {f : G → H} :
    (m : ℕ) → {A : StratObj G m} → {B : StratObj H m} → (η : StratHom f m A B) →
      StratHom.comp m η (StratHom.id m B) = η
  | 0, _, _, _ => rfl
  | m + 1, _, _, η => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun s =>
      Prod.ext rfl (StratHom.comp_id m ((η x).2 s).2)))

theorem StratHom.assoc {G H K L : Type} {f : G → H} {g : H → K} {h : K → L} :
    (m : ℕ) → {A : StratObj G m} → {B : StratObj H m} → {C : StratObj K m} → {D : StratObj L m} →
      (η : StratHom f m A B) → (θ : StratHom g m B C) → (κ : StratHom h m C D) →
      StratHom.comp m (StratHom.comp m η θ) κ = StratHom.comp m η (StratHom.comp m θ κ)
  | 0, _, _, _, _, _, _, _ => rfl
  | m + 1, _, _, _, _, η, θ, κ => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun s =>
      Prod.ext rfl (StratHom.assoc m ((η x).2 s).2 ((θ (f x)).2 ((η x).1 s)).2
        ((κ (g (f x))).2 ((θ (f x)).1 ((η x).1 s))).2)))

/-- The **total category of `m`-strategies** `Strat^σ_m` (¶5.50, p.28), objects: "a triple (G, β, A), where
(G, β) ∈ Pos^σ_m and A ∈ Ob(Strat_m(G, β))". -/
structure StratTot (σ : Sig) (m k : ℕ) : Type 1 where
  /-- The position `(G, β)`. -/
  pos : Pos σ k
  /-- The strategy `A ∈ Strat_m(G, β)`. -/
  obj : StratObj pos.carrier m

variable {σ : Sig} {m k : ℕ}

/-- A morphism `(f, η) : (G, β, A) → (H, γ, B)` of the total category (¶5.50, p.28): "a morphism of positions
f : (G, β) → (H, γ) together with a morphism η : f_* A → B in Strat_m(H, γ)", the latter written as a morphism
over `f` (`StratHom`). -/
@[ext] structure StratTot.Hom (X Y : StratTot σ m k) : Type where
  /-- The morphism of positions. -/
  pos : X.pos ⟶ Y.pos
  /-- The morphism `f_* A → B`. -/
  obj : StratHom pos.1 m X.obj Y.obj

/-- **The total category of `m`-strategies** `Strat^σ_m` (¶5.50, p.28): identities `(id_G, id_A)` and composition
`(g, θ) ∘ (f, η) := (gf, θ ∘ g_*(η))`. This is the Grothendieck construction of the pseudofunctor
`(G, β) ↦ Strat_m(G, β)` (footnote 11, p.28), presented by morphisms over maps of positions.

**Formalization Note** A morphism over `f` is a morphism `f_* A → B` in the fibre, written out (see `StratHom`),
so the coherence isomorphisms `(id)_* ≅ id` and `(gf)_* ≅ g_* f_*` that footnote 11 suppresses are built into
`StratHom.id` and `StratHom.comp`; the category laws hold on the nose. -/
instance StratTot.category : Category.{0} (StratTot σ m k) where
  Hom X Y := StratTot.Hom X Y
  id X := ⟨𝟙 X.pos, StratHom.id m X.obj⟩
  comp F G := ⟨F.pos ≫ G.pos, StratHom.comp (f := F.pos.1) (g := G.pos.1) m F.obj G.obj⟩
  id_comp F := StratTot.Hom.ext rfl (heq_of_eq (StratHom.id_comp (f := F.pos.1) m F.obj))
  comp_id F := StratTot.Hom.ext rfl (heq_of_eq (StratHom.comp_id (f := F.pos.1) m F.obj))
  assoc F G H := StratTot.Hom.ext rfl (heq_of_eq
    (StratHom.assoc (f := F.pos.1) (g := G.pos.1) (h := H.pos.1) m F.obj G.obj H.obj))

/-- The **projection functor** `p : Strat^σ_m → Pos^σ_m` (footnote 11, p.28), forgetting the strategy. -/
def StratTot.proj (σ : Sig) (m k : ℕ) : StratTot σ m k ⥤ Pos σ k where
  obj X := X.pos
  map {X Y} (F : StratTot.Hom X Y) := F.pos
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The **projection** `f_* A` of a strategy along `f : G → H` (Proposition 5.44, p.26; Eq. (8)–(10) in the proof
of Lemma 5.56, p.31): at level `m + 1`, for each `x' ∈ H`, the concatenation over `x ∈ f⁻¹(x')` of the families of
responses `A(x)`, each response `(y, A')` sent to `(f(y), f_* A')`. A point with empty preimage gets the empty
family; distinct responses with the same image stay distinct entries (Example 5.45, p.27). -/
def StratObj.push {G H : Type} (f : G → H) : (m : ℕ) → StratObj G m → StratObj H m
  | 0, _ => PUnit.unit
  | m + 1, A => fun x' =>
      ⟨Σ x : {x : G // f x = x'}, (A x.1).idx, fun p =>
        (f ((A p.1.1).obj p.2).1, StratObj.push f m ((A p.1.1).obj p.2).2)⟩

/-- The morphism `(f, 𝟙) : (G, β, A) → (H, fβ, f_* A)` over `f`: the identity of `f_* A`, written as a morphism
over `f`. -/
def StratObj.pushHom {G H : Type} (f : G → H) : (m : ℕ) → (A : StratObj G m) →
    StratHom f m A (StratObj.push f m A)
  | 0, _ => PUnit.unit
  | m + 1, A => fun x =>
      ⟨fun s => ⟨⟨x, rfl⟩, s⟩, fun s => ⟨⟨rfl⟩, StratObj.pushHom f m ((A x).obj s).2⟩⟩

/-- The **canonical coherence isomorphism** `g_*(f_* A) ≅ h_* A` for `h = g ∘ f`, written as a morphism over `g`
from `f_* A` to `h_* A` (footnote 11, p.28: "(gf)_* ≅ g_* f_*"). At level `m + 1` it sends the entry of
`(f_* A)(x')` indexed by `(x, s)`, `f x = x'`, to the entry of `(h_* A)(g x')` with the same index `(x, s)`. -/
def StratObj.pushComp {G H K : Type} (f : G → H) (g : H → K) (h : G → K) (hgf : ∀ x, g (f x) = h x) :
    (m : ℕ) → (A : StratObj G m) → StratHom g m (StratObj.push f m A) (StratObj.push h m A)
  | 0, _ => PUnit.unit
  | m + 1, A => fun x' =>
      ⟨fun p => ⟨⟨p.1.1, by rw [← hgf, p.1.2]⟩, p.2⟩, fun p =>
        ⟨⟨hgf _⟩, StratObj.pushComp f g h hgf m ((A p.1.1).obj p.2).2⟩⟩

end Supplement

end CoDecompFO


