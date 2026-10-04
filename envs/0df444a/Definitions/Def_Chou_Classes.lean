-- Prove2me | Definitions.Def_Chou_Classes
-- name    : Chou_Classes
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-19T11:40:17.908093+00:00
-- url     : https://prove2.me/theorems/cfbed788-86fa-4d0e-bbad-dfc9c07a638c
-- title:
--   Chou's classes: constructible groups, locally finite groups, $NF$, packings and property (P)
-- statement:
--   The classes of groups of the paper, on top of the published `Chou.ElementaryAmenable`.
--
--   - p. 397: “Let $EG_0$ be the class of all finite groups and all abelian groups. Assume that
--     $\alpha > 0$ is an ordinal and that we have defined $EG_\beta$ for each ordinal $\beta < \alpha$.
--     Then if $\alpha$ is a limit ordinal, set $EG_\alpha = \bigcup\{EG_\beta: \beta < \alpha\}$ and if
--     $\alpha$ is not a limit ordinal, set $EG_\alpha$ is the class of groups which can be obtained
--     from groups in $EG_{\alpha-1}$ by applying either process (III) or process (IV) once and only
--     once.” The processes are named on p. 396, “(III) *group extensions* and (IV) *direct
--     unions*”; the source does not define a direct union, and it names the union of the
--     $EG_\alpha$ only in Proposition 2.2 and its proof (p. 397: “Let
--     $EG' = \bigcup_\alpha EG_\alpha$.”).
--     `Constructible G`: $G$ lies in the smallest class of groups containing all finite groups and
--     all abelian groups and closed under isomorphism, extensions and directed unions of subgroups,
--     each rule stated precisely as a constructor. It stands in for Chou's $\bigcup_\alpha EG_\alpha$ (the
--     identification is the mission's Proposition 2.2(b) statement), the class obtained from $EG_0$ by processes (III) and (IV) only, as one inductive predicate.
--   - p. 398: “Recall that a group $G$ is periodic if each element of $G$ is of finite order and $G$
--     is locally finite if each finitely generated subgroup is finite.” `IsLocallyFinite G`: every
--     finitely generated subgroup of $G$ is finite. (Periodic groups are Mathlib's `IsMulTorsion`.)
--   - p. 396: “Therefore, $NF$, the class of groups without free subgroup on two generators, contains
--     $AG$.” ($AG$ is the class of amenable groups.) `NoFreeSubgroupOfRankTwo G`: Day's class
--     $NF$ — no homomorphism from the free group on two generators into $G$ is injective.
--   - p. 403: “For convenience, we will say that the pair $(S, X)$ forms a packing of $G$.” The
--     sentence names the condition that ends the definition of property $(P)$ just before it (quoted
--     below). `IsPacking S X`: the map $(s, x) \mapsto s\,x$ is a bijection $S \times X \to G$.
--   - pp. 402–403, Definition: “A group $G$ is said to have property $(P)$ if given a finite set $F$
--     in $G$ there exist a finite set $S \supset F$ and a set $X$ in $G$ such that the mapping from
--     $S \times X$ to $G$ which sends $(s, x)$ to $s \cdot x$, $s \in S$, $x \in X$, is one-one and
--     onto.” (The source's $\supset$ is not strict.) `HasPackingProperty G`: property $(P)$ — for
--     every finite $F \subseteq G$ there are a finite $S \supseteq F$ and a set $X$ with $(S, X)$ a
--     packing of $G$.
--   - p. 405, Corollary 4.7: “If $G$ is residually in $EG$, i.e., for each $x \ne e$ in $G$ there
--     exists a normal subgroup $K$ of $G$ such that $x \notin K$ and $G/K \in EG$, then $G$ has
--     property $(P)$.” The definition is the “i.e.” clause; the source has no separate defining
--     sentence. `ResiduallyElementaryAmenable G`: for every $x \ne 1$ there is a normal subgroup $K$
--     with $x \notin K$ and $G/K$ elementary amenable.
--
--   No theorem is stated here.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, §2 p. 397 (EG_α), p. 398 (periodic, locally finite), §1 p. 396 (NF), §4 pp. 402–403 (packings, property (P)), Corollary 4.7 p. 405 (residually in EG)

import Definitions.Def_Chou_ElementaryAmenable
import Mathlib

/-!
# Chou's classes of groups: the constructible groups, periodic and locally finite groups,
groups without free subgroups, and the packing property (P)

Chou, *Elementary amenable groups*, Illinois J. Math. 24 (1980) 396–407.

* `Constructible` (§2, p. 397): Chou builds `EG_α` by transfinite recursion, applying only the
  processes (III) group extension and (IV) direct union to the class `EG₀` of finite and abelian
  groups, and shows (Proposition 2.2) that `⋃_α EG_α` is all of `EG`.  The union `⋃_α EG_α` is
  realised here as one inductive predicate, whose structural induction is Chou's transfinite
  induction.  Closure under isomorphism is a constructor, as in `ElementaryAmenable`.
* Periodic and locally finite groups (§2, p. 398): Mathlib's `IsMulTorsion G` is "periodic";
  `IsLocallyFinite` is defined here.
* `NoFreeSubgroupOfRankTwo` (§1, p. 396): Day's class `NF`.
* Packings and property (P) (§4, p. 402): a pair `(S, X)` with `(s, x) ↦ s * x` a bijection
  `S × X → G`; property (P) asks every finite set to lie in a finite `S` of some packing.
* `ResiduallyElementaryAmenable` (Corollary 4.7, p. 405).
-/

universe u

namespace Chou

/-- `Constructible G`: `G` lies in the smallest class of groups containing all finite groups
and all abelian groups and closed under isomorphism, extensions and directed unions of
subgroups — Chou's `⋃_α EG_α`, built from `EG₀` by processes (III) and (IV) only. -/
inductive Constructible : (G : Type u) → [Group G] → Prop
  /-- Every finite group is constructible. -/
  | of_finite (G : Type u) [Group G] [Finite G] : Constructible G
  /-- Every abelian group is constructible. -/
  | of_commGroup (G : Type u) [CommGroup G] : Constructible G
  /-- The class is closed under isomorphism. -/
  | of_mulEquiv {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
      Constructible G → Constructible H
  /-- Process (III): if `N` is normal in `G` with `N` and `G ⧸ N` constructible, so is `G`. -/
  | extension {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
      Constructible N → Constructible (G ⧸ N) → Constructible G
  /-- Process (IV): a directed union of constructible subgroups is constructible. -/
  | directedUnion {G : Type u} [Group G] {ι : Type u} (H : ι → Subgroup G)
      (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) :
      (∀ i, Constructible (H i)) → Constructible G

/-- A group is **locally finite** if each of its finitely generated subgroups is finite
(p. 398). -/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, S.Finite → Finite (Subgroup.closure S)

/-- Day's class `NF` (p. 396): `G` contains no free subgroup on two generators, i.e. no
homomorphism from the free group on two generators into `G` is injective. -/
def NoFreeSubgroupOfRankTwo (G : Type*) [Group G] : Prop :=
  ∀ f : FreeGroup (Fin 2) →* G, ¬ Function.Injective f

/-- `(S, X)` is a **packing** of `G` (p. 403): the map `(s, x) ↦ s * x` from `S × X` to `G` is
one-to-one and onto. -/
def IsPacking {G : Type*} [Group G] (S X : Set G) : Prop :=
  Set.BijOn (fun p : G × G => p.1 * p.2) (S ×ˢ X) Set.univ

/-- **Property (P)** (p. 402): for every finite subset `F` of `G` there are a finite set
`S ⊇ F` and a set `X` such that `(S, X)` is a packing of `G`. -/
def HasPackingProperty (G : Type*) [Group G] : Prop :=
  ∀ F : Set G, F.Finite → ∃ S X : Set G, F ⊆ S ∧ S.Finite ∧ IsPacking S X

/-- `G` is **residually in `EG`** (Corollary 4.7, p. 405): for each `x ≠ 1` there is a normal
subgroup `K` with `x ∉ K` and `G ⧸ K` elementary amenable. -/
def ResiduallyElementaryAmenable (G : Type u) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → ∃ (K : Subgroup G) (_ : K.Normal), x ∉ K ∧ ElementaryAmenable (G ⧸ K)

end Chou


