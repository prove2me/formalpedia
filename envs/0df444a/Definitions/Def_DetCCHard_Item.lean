-- Prove2me | Definitions.Def_DetCCHard_Item
-- name    : DetCCHard_Item
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:02.661995+00:00
-- url     : https://prove2.me/theorems/8ac62750-6598-49b6-8751-0c66e98da304
-- title:
--   Items, active coordinates and collisions of the source construction
-- statement:
--   Let $s \ge 4$ be a power of two and $G = (V, E)$ a source graph with $n$ vertices. An **item** is a vertex or an auxiliary label in one of $4s$ groups: $I = [4s] \times (V \sqcup [s-3])$. Items $(g, v)$ with $v \in V$ are **vertex items**, items $(g, a)$ with $a \in [s-3]$ are **auxiliary items**.
--
--   Each edge occurrence in each group has one base coordinate, at which its two endpoints and the $s - 3$ auxiliary items of that group are **active**; all other items are inactive there. These $4s|E|$ base coordinates are padded with inactive coordinates to $q_0 = \mathrm{pow2}(4s|E|)$, and each is repeated $q_2/q_0 = 2^t$ times, giving indices $\alpha \in [q_2]$. A **collision** at $\alpha$ for an assignment $\chi$ of a set $R$ of retained items to the $s$ bins is a bin containing two distinct retained items active at $\alpha$ and a retained item inactive at $\alpha$.
--
--   Collisions are what force the extra bit of the NO case (Lemma 6.3).
--
--   **Formalization Note** The paper leaves the order of the base coordinates open ("a fixed order"). Here base coordinate $\beta < 4s|E|$ is edge occurrence $\beta \bmod |E|$ of group $\lfloor \beta / |E| \rfloor$, larger $\beta$ are padding, and index $\alpha$ repeats base coordinate $\lfloor \alpha / 2^t \rfloor$. The number of collision coordinates does not depend on this choice. An assignment is a function on all items; only its values on $R$ matter.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 6.2 (Active items), p.19, and §6.2, p.19

import Mathlib
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2

namespace DetCCHard

/-- The **items** of the source construction (Gaspers–He–Mackenzie, arXiv:2508.05597, held version
sha256 ad552d13…a4a03, Definition 6.2, "Active items", p.19): `I = [4s] × (V ⊔ [s − 3])`, a
vertex (`Sum.inl v`) or an auxiliary label (`Sum.inr a`) in one of `4s` groups. The items
`(g, inl v)` are the **vertex items**, the items `(g, inr a)` the **auxiliary items**.

**Formalization Note** Groups, vertices and auxiliary labels are indexed from `0`. -/
abbrev Item (s n : ℕ) : Type := Fin (4 * s) × (Fin n ⊕ Fin (s - 3))

/-- The padded number of base coordinates `q₀ = pow2(4s|E|)` (Definition 6.2, p.19). -/
def baseCoordCount (G : SrcGraph) (s : ℕ) : ℕ := pow2 (4 * s * G.edges.length)

/-- **Activity of an item at a coordinate** (Definition 6.2, p.19): `v_i(α) = 1`. Each of the
`4s|E|` (group, edge occurrence) pairs has one base coordinate, at which the two endpoints of the
edge occurrence and the `s − 3` auxiliary items of that group are active; the base coordinates are
padded with inactive coordinates to `q₀`, and each base coordinate is repeated `2^t = q₂/q₀` times,
so the index `α ∈ [q₂]`, `q₂ = q₀·2^t`, repeats base coordinate `β = ⌊α / 2^t⌋`.

**Formalization Note** The paper leaves the order of the base coordinates and of the repetitions
open; here base coordinate `β < 4s|E|` is edge occurrence `β mod |E|` of group `⌊β/|E|⌋`, base
coordinates `β ≥ 4s|E|` are padding, and copies of one base coordinate are consecutive. The number
of collision coordinates in Lemma 6.3 does not depend on this choice. -/
def active (G : SrcGraph) (s t : ℕ) (i : Item s G.n) (α : ℕ) : Prop :=
  α / 2 ^ t < 4 * s * G.edges.length ∧
    (i.1 : ℕ) = α / 2 ^ t / G.edges.length ∧
    match i.2 with
    | Sum.inl v => ∃ e ∈ G.edges[α / 2 ^ t % G.edges.length]?, v = e.1 ∨ v = e.2
    | Sum.inr _ => True

/-- A **collision** at coordinate `α` for an assignment `χ` of the retained items `R` to the `s`
bins (Definition 6.2, p.19, and §6.2, p.19: "a coordinate at which one bin contains two active
items and an inactive item"): some bin contains two distinct retained items active at `α` and a
retained item inactive at `α`.

**Formalization Note** The assignment is a function on all items; only its values on `R` matter. -/
def IsCollision (G : SrcGraph) (s t : ℕ) (R : Set (Item s G.n)) (χ : Item s G.n → Fin s)
    (α : ℕ) : Prop :=
  ∃ i₁ ∈ R, ∃ i₂ ∈ R, ∃ i₃ ∈ R, i₁ ≠ i₂ ∧ χ i₁ = χ i₂ ∧ χ i₃ = χ i₁ ∧
    active G s t i₁ α ∧ active G s t i₂ α ∧ ¬ active G s t i₃ α

end DetCCHard


