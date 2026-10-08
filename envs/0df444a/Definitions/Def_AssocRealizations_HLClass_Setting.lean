-- Prove2me | Definitions.Def_AssocRealizations_HLClass_Setting
-- name    : AssocRealizations_HLClass_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:32.014621+00:00
-- url     : https://prove2.me/theorems/efb4dfb4-8aa2-4f5a-afa5-041560552826
-- title:
--   Definitions 2.1 and 4.1, p. 17 — normal isomorphism, Hohlweg–Lange normal vectors and fans, reflection and reversal of sign sequences
-- statement:
--   This file fixes the objects of the classification of the Hohlweg–Lange associahedra up to normal isomorphism.
--
--   **The polygon.** Let $n \ge 0$ and $N = n+3$. The vertices of a convex $N$-gon are the positions $0, 1, \dots, N-1$ in counterclockwise order. A *chord* is an unordered pair of positions; a *diagonal* joins two distinct, non-adjacent positions, and two chords *cross* when their four endpoints are distinct and alternate around the boundary (the published polygon conventions of `ChvatalArtGallery.FanPartition.Triangulation`). The *dihedral symmetries* are the $2N$ maps $i \mapsto r+i$ and $i \mapsto r-i$ (indices mod $N$).
--
--   **Fans and normal isomorphism.** Given a vector $v_\delta$ in a real vector space $V$ for every chord $\delta$, its fan is the set of cones
--   $$\mathbb R_{\ge 0}\{v_\delta : \delta \in D\},$$
--   one for each set $D$ of pairwise non-crossing diagonals (the empty set gives $\{0\}$). Following Definition 2.1, two fans $\mathcal F \subseteq 2^V$ and $\mathcal G \subseteq 2^W$ are *linearly (normally) isomorphic* if some linear isomorphism $L : V \to W$ sends each cone of $\mathcal F$ to a cone of $\mathcal G$. Two facet normals $v, w$ are *opposite* (the facets are parallel) if $v = -c\,w$ for some $c > 0$.
--
--   **The Hohlweg–Lange polygon.** For a sign sequence $\sigma \in \{+,-\}^{n-1}$ put $\widetilde\sigma = \{+,-,\sigma,-,+\}$: the labels $0, \dots, n+2$ carry the signs $+$ (label $0$), $-$ (label $1$), $\sigma_1, \dots, \sigma_{n-1}$ (labels $2, \dots, n$), $-$ (label $n+1$), $+$ (label $n+2$). Placing the labels from left to right, the positive ones above and the negative ones below a horizontal line, gives a convex polygon $P_{n+3}(\sigma)$. Its counterclockwise boundary visits the negative labels in increasing order and then the positive labels in decreasing order; this fixes which label sits at which position.
--
--   **Definition 4.1.** For a diagonal $ij$ of $P_{n+3}(\sigma)$ with labels $i<j$, $R_{ij}(\sigma)$ is the set of vertices strictly below it, i.e. the labels strictly inside the counterclockwise boundary arc from $i$ to $j$. $S_{ij}(\sigma)$ is obtained from $R_{ij}(\sigma)$ by replacing $0$ by $i$ (if $0 \in R_{ij}$) and $n+2$ by $j$ (if $n+2 \in R_{ij}$); it is a subset of $[n+1] = \{1, \dots, n+1\}$. The facet of the Hohlweg–Lange associahedron $\mathrm{Ass}^I_n(\sigma)$ for $\delta$ has normal vector $e_{S_\delta(\sigma)}$, considered modulo $e_{[n+1]} = (1,\dots,1)$. Concretely, the normal vector used here is
--   $$v_\delta(\sigma) = \big(\mathbf 1[k \in S_\delta(\sigma)] - \mathbf 1[n+1 \in S_\delta(\sigma)]\big)_{k=1,\dots,n} \in \mathbb R^n,$$
--   the image of $e_{S_\delta(\sigma)}$ under $x \mapsto (x_k - x_{n+1})_{k \le n}$, whose kernel is $\mathbb R\,e_{[n+1]}$. The normal fan of $\mathrm{Ass}^I_n(\sigma)$ is the fan of these vectors.
--
--   **Reflection and reversal.** The reflection of $\sigma$ is $-\sigma$ (every sign flipped), the reversal $\sigma^t$ reverses the order of the entries. As the two operations are commuting involutions, "$\sigma_2$ can be obtained from $\sigma_1$ by reflections and reversals" means $\sigma_2 \in \{\sigma_1, -\sigma_1, \sigma_1^t, -\sigma_1^t\}$.
--
--   These objects are shared by every statement of the mission: the goal (Theorem 4.9) compares the fans of two sign sequences, and the milestones describe their parallel facets and the symmetries between them.
--
--   **Formalization Note** Signs are `Bool` (`true` = $+$) and $\sigma$ is a function `Fin (n - 1) → Bool`. Positions and labels are both `Fin (n + 3)`; `hlLabel n σ p` is the label at position `p`. Cones are nonnegative spans (`Submodule.span` over $\mathbb R_{\ge 0}$). That the maximal cones of the fan of $v(\sigma)$ are exactly the triangulations of $P_{n+3}(\sigma)$, so that this is the normal fan of $\mathrm{Ass}^I_n(\sigma)$, is Hohlweg–Lange's theorem (Proposition 4.3 of the paper); the fan-level encoding relies on it. Linear-isomorphism classes do not depend on the choice of the projection modulo $e_{[n+1]}$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 5, 14–17, Definition 2.1, §4.1, Definition 4.1, §4.2 (p. 16) and the definition of reflection and reversal (p. 17)

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-!
Ceballos, Santos and Ziegler, *Many non-equivalent realizations of the associahedron*,
arXiv:1109.5544v2: Definition 2.1 (p. 5), §4.1 (pp. 14–15, Definition 4.1) and the reflection
and reversal of sign sequences (p. 17).

The convex (n + 3)-gon has vertex set `Fin (n + 3)`, read as **positions** in counterclockwise
boundary order (the convention of `ChvatalArtGallery.FanPartition`). Diagonals are elements of
`Sym2 (Fin (n + 3))`. The Hohlweg–Lange polygon `P_{n+3}(σ)` carries its own **labels**
`0, …, n + 2` (left-to-right order); `hlLabel n σ p` is the label at position `p`.
-/

/-- The sign word `σ̃ = {+, −, σ, −, +}` (p. 15) of the labels `0, …, n + 2`, with `true` for
`+`: label `0` and `n + 2` are `+`, labels `1` and `n + 1` are `−`, and label `k` with
`2 ≤ k ≤ n` carries `σ_{k-1}` (the `(k - 2)`-th entry of `σ : Fin (n - 1) → Bool`, 0-based).
Arguments beyond `n + 2` are never used. -/
def hlSign (n : ℕ) (σ : Fin (n - 1) → Bool) (k : ℕ) : Bool :=
  if k = 0 then true
  else if k = 1 then false
  else if k = n + 1 then false
  else if k = n + 2 then true
  else if h : k - 2 < n - 1 then σ ⟨k - 2, h⟩ else true

/-- The labels of `P_{n+3}(σ)` in counterclockwise boundary order: the negative labels in
increasing order (the lower chain, left to right), then the positive labels in decreasing order
(the upper chain, right to left). -/
def hlOrder (n : ℕ) (σ : Fin (n - 1) → Bool) : List (Fin (n + 3)) :=
  (List.finRange (n + 3)).filter (fun k => !hlSign n σ k.val) ++
    ((List.finRange (n + 3)).filter (fun k => hlSign n σ k.val)).reverse

/-- The label of `P_{n+3}(σ)` at position `p`. -/
def hlLabel (n : ℕ) (σ : Fin (n - 1) → Bool) (p : Fin (n + 3)) : Fin (n + 3) :=
  (hlOrder n σ).getD p.val 0

/-- For the chord with endpoints at positions `p, q` (to be used when `hlLabel p < hlLabel q`):
`R_{ij}(σ)`, the labels at the positions strictly inside the counterclockwise arc from `p` to
`q`, i.e. the vertices strictly below the diagonal `ij` (Definition 4.1). -/
def hlROrd (n : ℕ) (σ : Fin (n - 1) → Bool) (p q : Fin (n + 3)) : Finset (Fin (n + 3)) :=
  (Finset.univ.filter (fun x : Fin (n + 3) => 0 < cdist p x ∧ cdist p x < cdist p q)).image
    (hlLabel n σ)

/-- `S_{ij}(σ)` for the chord at positions `p, q` with labels `i = hlLabel p < j = hlLabel q`
(Definition 4.1): `R_{ij}(σ)` with `0` replaced by `i` and `n + 2` replaced by `j`. -/
def hlSOrd (n : ℕ) (σ : Fin (n - 1) → Bool) (p q : Fin (n + 3)) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun k : Fin (n + 3) =>
    (k.val ≠ 0 ∧ k.val ≠ n + 2 ∧ k ∈ hlROrd n σ p q) ∨
    (k = hlLabel n σ p ∧ ∃ z ∈ hlROrd n σ p q, z.val = 0) ∨
    (k = hlLabel n σ q ∧ ∃ z ∈ hlROrd n σ p q, z.val = n + 2))

/-- `S_δ(σ)` (Definition 4.1) of a chord `δ` given by positions, as a set of labels: the chord is
oriented so that its first endpoint has the smaller label. -/
def hlS (n : ℕ) (σ : Fin (n - 1) → Bool) (e : Sym2 (Fin (n + 3))) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun k : Fin (n + 3) =>
    ∃ p q : Fin (n + 3), e = s(p, q) ∧ hlLabel n σ p < hlLabel n σ q ∧ k ∈ hlSOrd n σ p q)

/-- The normal vector `e_{S_δ(σ)}` of the facet of `Ass^I_n(σ)` for the chord `δ`, taken modulo
`e_{[n+1]} = (1, …, 1)` (p. 16) through the linear map `x ↦ (x_k - x_{n+1})_{k = 1, …, n}`
of `ℝ^{n+1}` onto `ℝ^n` (kernel `ℝ · e_{[n+1]}`). Coordinate `k : Fin n` is label `k + 1`. -/
noncomputable def hlVec (n : ℕ) (σ : Fin (n - 1) → Bool) (e : Sym2 (Fin (n + 3))) : Fin n → ℝ :=
  fun k => (if (⟨k.val + 1, by omega⟩ : Fin (n + 3)) ∈ hlS n σ e then (1 : ℝ) else 0) -
    (if (⟨n + 1, by omega⟩ : Fin (n + 3)) ∈ hlS n σ e then (1 : ℝ) else 0)

/-- The normal fan of the Hohlweg–Lange associahedron `Ass^I_n(σ)` (Definition 4.1), in the
coordinates of `hlVec`: one cone per set of pairwise non-crossing diagonals of `P_{n+3}(σ)`
(Hohlweg–Lange, Prop. 4.3 of the paper). -/
noncomputable def hlFan (n : ℕ) (σ : Fin (n - 1) → Bool) : Set (Set (Fin n → ℝ)) :=
  AssocRealizations.TypesMeet.rayFan (hlVec n σ)

/-- The reflection `-σ` of a sign sequence (p. 17): every sign flipped. -/
def negSigma {m : ℕ} (σ : Fin m → Bool) : Fin m → Bool := fun i => !σ i

/-- The reversal `σ^t` of a sign sequence (p. 17): the order of the coordinates reversed. -/
def revSigma {m : ℕ} (σ : Fin m → Bool) : Fin m → Bool := fun i => σ (Fin.rev i)

/-- `σ₂` is obtained from `σ₁` by reflections and reversals: the two operations are commuting
involutions, so the orbit of `σ₁` is `{σ₁, -σ₁, σ₁^t, -σ₁^t}`. -/
def SignEquiv {m : ℕ} (σ₁ σ₂ : Fin m → Bool) : Prop :=
  σ₂ = σ₁ ∨ σ₂ = negSigma σ₁ ∨ σ₂ = revSigma σ₁ ∨ σ₂ = negSigma (revSigma σ₁)

end AssocRealizations.HLClass


