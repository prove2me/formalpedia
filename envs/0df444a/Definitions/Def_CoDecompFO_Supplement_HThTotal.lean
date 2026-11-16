-- Prove2me | Definitions.Def_CoDecompFO_Supplement_HThTotal
-- name    : CoDecompFO_Supplement_HThTotal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:47:24.345219+00:00
-- url     : https://prove2.me/theorems/5e32e997-0df7-4f80-a6ef-e920c620f2e4
-- title:
--   Diagrammatic $m$-hypotheticals $\mathrm{HTh}_m(G,\beta)$ and the total category $\mathrm{HTh}^\sigma_m$
-- statement:
--   1. **Hypotheses** (¶4.7, ¶4.9, ¶5.12). A hypothesis with underlying assignment $\beta:[k]\to G$ is a structure $N$ on $[k]$ (a set of atoms $R(i_1,\dots,i_a)$ on $[k]$) such that $\beta:N\to G$ is a homomorphism. A morphism of hypotheses over $\mathrm{id}$ is a homomorphism of heads with identity underlying function, i.e. an inclusion of atom sets.
--
--   2. **Diagrammatic hypotheticals** (¶5.35, Eq. (4)). $\mathrm{HTh}_0(G,\beta)=\mathrm{Fam}(\mathrm{Hyp}(G,\beta))$ and
--   $$\mathrm{HTh}_m(G,\beta)=\prod_{x\in G}\mathrm{Fam}\Big(\mathrm{Fam}\Big(\sum_{y\in G}\mathrm{HTh}_{m-1}(G,\beta\cdot x\cdot y)\Big)\Big):$$
--   for each move $x$, a family of personalities, each a family of responses $(y,A')$. Here $\beta\cdot x\cdot y$ is the continuation of $\beta$ by $x$ and then $y$ (¶5.8).
--
--   3. **Total category** (¶5.50). Objects $(G,\beta,A)$ with $A\in\mathrm{HTh}_m(G,\beta)$; a morphism is a morphism of positions $f$ with $\eta:f_*A\to B$, where $f_*$ postcomposes hypotheses with $f$ (heads unchanged), concatenates personalities over each fibre $f^{-1}(x')$ and keeps each personality's responses, tagging $y$ by $f(y)$ (Prop. 5.44, Example 5.45). The projection functor to $\mathrm{Pos}^\sigma_m$ forgets $A$.
--
--   **Formalization Note** As for strategies, $\eta:f_*A\to B$ is written out through the universal property of the concatenations: for each $x$ a map of personalities, for each personality a map of responses, for each response the equation $f(y)=y'$ and a morphism one level down; at level $0$ an index map with inclusions of atom sets. Raw hypotheticals carry the condition that every leaf hypothesis lies over its assignment as a separate field.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶4.7–4.9, pp.10–11; ¶5.8 and ¶5.12, pp.18–19; ¶5.35 (Eq. 4), p.24; Prop. 5.44 and Example 5.45, pp.26–27; ¶5.48–5.50, pp.27–28 (PDF pp.12–30)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_StratTotal
import Definitions.Def_CoDecompFO_AltSat

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory FirstOrder

/-- `N` is the head of a **hypothesis with underlying assignment `β`** (¶4.7, p.10; ¶5.12, p.19): "A hypothesis
in a structure G is a homomorphism N →ν G where N = [ℓ]", here with underlying function `β : [k] → G`. The head
is the structure `head N` on `[k]` whose relations are the atoms in `N` (published `CoDecompFO.head`). -/
def IsHypOver {σ : Sig} {G : Type} [σ.lang.Structure G] {k : ℕ} (β : Fin k → G)
    (N : Set (σ.Atom k)) : Prop :=
  @IsHom σ (Fin k) G (head N) _ β

/-- The objects of the category `HTh_m(G, β)` of **diagrammatic `m`-hypotheticals** (¶5.35, Eq. (4), p.24),
before the condition that the hypotheses have the right underlying assignment (`HThValid`):
`HTh_0(G, β) := Fam(Hyp(G, β))` and `HTh_m(G, β) := ∏_{x∈G} Fam(Fam(∑_{y∈G} HTh_{m−1}(G, β·x·y)))`. A hypothesis
is represented by its head, a set of atoms on `[k]`. -/
def HThObj (σ : Sig) (G : Type) : ℕ → ℕ → Type 1
  | 0, k => Fam (ULift.{1} (Set (σ.Atom k)))
  | m + 1, k => G → Fam (Fam (G × HThObj σ G m (k + 2)))

/-- The **continuation** `β·x·y` of a partial assignment (¶5.8, p.18): `β` followed by `x` at the next index and
`y` at the one after. -/
def cont {G : Type} {k : ℕ} (β : Fin k → G) (x y : G) : Fin (k + 2) → G :=
  Fin.snoc (Fin.snoc β x) y

/-- A raw hypothetical lies in `HTh_m(G, β)`: every hypothesis at the leaves, reached through the moves
`x₁, y₁, …`, is a hypothesis with underlying assignment `β·x₁·y₁·…` (¶5.12, p.19; ¶5.35, p.24). -/
def HThValid {σ : Sig} {G : Type} [σ.lang.Structure G] : (m k : ℕ) → (Fin k → G) → HThObj σ G m k → Prop
  | 0, _, β, A => ∀ s, IsHypOver β (A.obj s).down
  | m + 1, k, β, A => ∀ x p r, HThValid m (k + 2) (cont β x (((A x).obj p).obj r).1)
      (((A x).obj p).obj r).2

/-- **Morphisms over a map `f : G → H`** between hypotheticals, `HThHom f m k A B`: the set of morphisms
`η : f_* A → B` in `HTh_m(H, fβ)`, with `f_*` the projection functor of Proposition 5.44 (p.26), written out as for
`StratHom`. At level `0`, `f_*` postcomposes each hypothesis with `f` and keeps its head (Observation 4.15, p.12),
and a morphism of hypotheses over `id_H` (¶4.9, p.11) is a homomorphism of heads with underlying function
`id_[k]`, i.e. an inclusion of atom sets; so a morphism is an index map `u` with `N_s ⊆ M_{u(s)}`. At level `m + 1`,
`f_*` concatenates the families of personalities over each fibre `f⁻¹(x')` and keeps each personality's family of
responses, sending a response `(y, A')` to `(f(y), f_* A')` (Example 5.45, p.26); a morphism is, for each `x ∈ G`,
a map `u` of personalities of `A(x)` to those of `B(f x)`, for each personality `p` a map `v` of its responses, and
for each response a proof that the response points correspond under `f` with a morphism over `f` one level down. -/
def HThHom {σ : Sig} {G H : Type} (f : G → H) :
    (m k : ℕ) → HThObj σ G m k → HThObj σ H m k → Type
  | 0, _, A, B => {u : A.idx → B.idx // ∀ s, (A.obj s).down ⊆ (B.obj (u s)).down}
  | m + 1, k, A, B => (x : G) → Σ u : (A x).idx → (B (f x)).idx, (p : (A x).idx) →
      Σ v : ((A x).obj p).idx → ((B (f x)).obj (u p)).idx, (r : ((A x).obj p).idx) →
        PLift (f (((A x).obj p).obj r).1 = (((B (f x)).obj (u p)).obj (v r)).1) ×
          HThHom f m (k + 2) (((A x).obj p).obj r).2 (((B (f x)).obj (u p)).obj (v r)).2

/-- The identity morphism over `id`. -/
def HThHom.id {σ : Sig} {G : Type} : (m k : ℕ) → (A : HThObj σ G m k) → HThHom (fun x : G => x) m k A A
  | 0, _, _ => ⟨fun s => s, fun _ => le_rfl⟩
  | m + 1, k, A => fun x => ⟨fun p => p, fun p => ⟨fun r => r, fun r =>
      ⟨⟨rfl⟩, HThHom.id m (k + 2) (((A x).obj p).obj r).2⟩⟩⟩

/-- Composition of morphisms over `f` and over `g`, a morphism over `g ∘ f` (¶5.50, p.28). -/
def HThHom.comp {σ : Sig} {G H K : Type} {f : G → H} {g : H → K} :
    (m k : ℕ) → {A : HThObj σ G m k} → {B : HThObj σ H m k} → {C : HThObj σ K m k} →
      HThHom f m k A B → HThHom g m k B C → HThHom (g ∘ f) m k A C
  | 0, _, _, _, _, η, θ => ⟨fun s => θ.1 (η.1 s), fun s => (η.2 s).trans (θ.2 (η.1 s))⟩
  | m + 1, k, _, _, _, η, θ => fun x =>
      ⟨fun p => (θ (f x)).1 ((η x).1 p), fun p =>
        ⟨fun r => ((θ (f x)).2 ((η x).1 p)).1 (((η x).2 p).1 r), fun r =>
          ⟨⟨(congrArg g (((η x).2 p).2 r).1.down).trans
              (((θ (f x)).2 ((η x).1 p)).2 (((η x).2 p).1 r)).1.down⟩,
            HThHom.comp m (k + 2) (((η x).2 p).2 r).2
              (((θ (f x)).2 ((η x).1 p)).2 (((η x).2 p).1 r)).2⟩⟩⟩

theorem HThHom.id_comp {σ : Sig} {G H : Type} {f : G → H} :
    (m k : ℕ) → {A : HThObj σ G m k} → {B : HThObj σ H m k} → (η : HThHom f m k A B) →
      HThHom.comp m k (HThHom.id m k A) η = η
  | 0, _, _, _, _ => rfl
  | m + 1, k, _, _, η => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun p =>
      Sigma.ext rfl (heq_of_eq (funext fun r =>
        Prod.ext rfl (HThHom.id_comp m (k + 2) (((η x).2 p).2 r).2)))))

theorem HThHom.comp_id {σ : Sig} {G H : Type} {f : G → H} :
    (m k : ℕ) → {A : HThObj σ G m k} → {B : HThObj σ H m k} → (η : HThHom f m k A B) →
      HThHom.comp m k η (HThHom.id m k B) = η
  | 0, _, _, _, _ => rfl
  | m + 1, k, _, _, η => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun p =>
      Sigma.ext rfl (heq_of_eq (funext fun r =>
        Prod.ext rfl (HThHom.comp_id m (k + 2) (((η x).2 p).2 r).2)))))

theorem HThHom.assoc {σ : Sig} {G H K L : Type} {f : G → H} {g : H → K} {h : K → L} :
    (m k : ℕ) → {A : HThObj σ G m k} → {B : HThObj σ H m k} → {C : HThObj σ K m k} →
      {D : HThObj σ L m k} → (η : HThHom f m k A B) → (θ : HThHom g m k B C) → (κ : HThHom h m k C D) →
      HThHom.comp m k (HThHom.comp m k η θ) κ = HThHom.comp m k η (HThHom.comp m k θ κ)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | m + 1, k, _, _, _, _, η, θ, κ => funext fun x => Sigma.ext rfl (heq_of_eq (funext fun p =>
      Sigma.ext rfl (heq_of_eq (funext fun r =>
        Prod.ext rfl (HThHom.assoc m (k + 2) (((η x).2 p).2 r).2
          (((θ (f x)).2 ((η x).1 p)).2 (((η x).2 p).1 r)).2
          (((κ (g (f x))).2 ((θ (f x)).1 ((η x).1 p))).2
            (((θ (f x)).2 ((η x).1 p)).1 (((η x).2 p).1 r))).2)))))

/-- The **total category of `m`-hypotheticals** `HTh^σ_m` (¶5.50, p.28), objects: "a triple (G, β, A), where
(G, β) ∈ Pos^σ_m and A ∈ Ob(HTh_m(G, β))". -/
structure HThTot (σ : Sig) (m k : ℕ) : Type 1 where
  /-- The position `(G, β)`. -/
  pos : Pos σ k
  /-- The hypothetical, as raw data. -/
  obj : HThObj σ pos.carrier m k
  /-- The hypothetical lies in `HTh_m(G, β)`. -/
  valid : HThValid m k pos.pt obj

variable {σ : Sig} {m k : ℕ}

/-- A morphism `(f, η) : (G, β, A) → (H, γ, B)` of the total category (¶5.50, p.28): a morphism of positions `f`
with a morphism `η : f_* A → B` in `HTh_m(H, γ)`, written as a morphism over `f` (`HThHom`). -/
@[ext] structure HThTot.Hom (X Y : HThTot σ m k) : Type where
  /-- The morphism of positions. -/
  pos : X.pos ⟶ Y.pos
  /-- The morphism `f_* A → B`. -/
  obj : HThHom pos.1 m k X.obj Y.obj

/-- **The total category of `m`-hypotheticals** `HTh^σ_m` (¶5.50, p.28), the Grothendieck construction of the
pseudofunctor `(G, β) ↦ HTh_m(G, β)` (footnote 11, p.28), presented by morphisms over maps of positions; as for
`StratTot.category`, the coherence isomorphisms are built into `HThHom.id` and `HThHom.comp`. -/
instance HThTot.category : Category.{0} (HThTot σ m k) where
  Hom X Y := HThTot.Hom X Y
  id X := ⟨𝟙 X.pos, HThHom.id m k X.obj⟩
  comp F G := ⟨F.pos ≫ G.pos, HThHom.comp (f := F.pos.1) (g := G.pos.1) m k F.obj G.obj⟩
  id_comp F := HThTot.Hom.ext rfl (heq_of_eq (HThHom.id_comp (f := F.pos.1) m k F.obj))
  comp_id F := HThTot.Hom.ext rfl (heq_of_eq (HThHom.comp_id (f := F.pos.1) m k F.obj))
  assoc F G H := HThTot.Hom.ext rfl (heq_of_eq
    (HThHom.assoc (f := F.pos.1) (g := G.pos.1) (h := H.pos.1) m k F.obj G.obj H.obj))

/-- The **projection functor** `p : HTh^σ_m → Pos^σ_m` (footnote 11, p.28), forgetting the hypothetical. -/
def HThTot.proj (σ : Sig) (m k : ℕ) : HThTot σ m k ⥤ Pos σ k where
  obj X := X.pos
  map {X Y} (F : HThTot.Hom X Y) := F.pos
  map_id _ := rfl
  map_comp _ _ := rfl

end Supplement

end CoDecompFO


