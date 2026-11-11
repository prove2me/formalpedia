-- Prove2me | Definitions.Def_SepMeasures_Hyp
-- name    : SepMeasures_Hyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:31.018614+00:00
-- url     : https://prove2.me/theorems/c3f5740f-a33c-460c-8bfa-ee5273c993a8
-- title:
--   §2.1, pp.11–12 — oriented hyperplanes $H=\{u\cdot x=c\}$, half-spaces $H^\pm$, signs $\sigma_H$, $\mathrm{Sep}(H)$ and strips $B(H,\eta)$
-- statement:
--   Let $\mathbb R^d$ carry its Euclidean structure. An **oriented affine hyperplane** is a pair $(u,c)$ with $u\in\mathbb R^d\setminus\{0\}$ and $c\in\mathbb R$, describing
--   $$H=\{x\in\mathbb R^d: u\cdot x=c\},\qquad H^+=\{x: u\cdot x>c\},\qquad H^-=\{x: u\cdot x<c\}.$$
--   The two half-spaces are open. The **sign function** $\sigma_H:\mathbb R^d\to\{-1,0,+1\}$ is $+1$ on $H^+$, $-1$ on $H^-$ and $0$ on $H$. The set of ordered pairs **strictly separated** by $H$ is
--   $$\mathrm{Sep}(H)=(H^+\times H^-)\cup(H^-\times H^+),$$
--   so a pair with a point on $H$ is not separated. For $\eta>0$ the **strip** around $H$ is $B(H,\eta)=\{x:\operatorname{dist}(x,H)\le\eta\}$, with the Euclidean distance.
--
--   These are the geometric objects of every statement of the mission: cut values, bisection, separation probabilities and the tilting lemma all refer to them.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin d)` (abbreviated `E d`). Reversing the orientation $(u,c)\mapsto(-u,-c)$ gives the same hyperplane, swaps $H^+$ and $H^-$ and leaves $\mathrm{Sep}(H)$ unchanged, so a supremum over oriented hyperplanes is the paper's supremum over $\mathbb H^d$.
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §2.1, p.11 (hyperplanes, half-spaces, Sep(H)); §2.1, p.12 (strips B(H, η)); §2.3, p.12 (σ_H)

import Mathlib

open MeasureTheory

namespace SepMeasures

/-- The ambient space `ℝ^d`, as `EuclideanSpace ℝ (Fin d)`.

Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), §2.1, pp.10–12.

**Formalization Note.** The Euclidean structure of this space is used only where the paper is
Euclidean: hyperplane equations `u · x = c`, Lebesgue measure (`volume`), the closed balls
`B(x, r)`, the distance `dist(x, H)` and the strips `B(H, η)` (p.12). Distances inside `L`,
`C(H)`, `W₁` and first moments use an arbitrary norm `N`, passed separately. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- An oriented affine hyperplane `H = {x ∈ ℝ^d | u · x = c}` with `u ≠ 0`
(Correa et al., manuscript sha256 96a86924…fa82f, §2.1, p.11).

**Formalization Note.** A geometric hyperplane has two orientations (`(u, c)` and `(-u, -c)`,
and positive rescalings), which give the same set `H`, swap `H⁺` and `H⁻`, and leave `Sep(H)`
unchanged; so a supremum over `Hyp d` is the paper's supremum over `ℍ^d`. -/
structure Hyp (d : ℕ) where
  /-- The normal vector. -/
  u : E d
  /-- The offset. -/
  c : ℝ
  /-- The normal vector is non-zero. -/
  hu : u ≠ 0

namespace Hyp

variable {d : ℕ}

/-- The hyperplane itself, `{x | u · x = c}` (p.11). -/
def set (H : Hyp d) : Set (E d) := {x | inner ℝ H.u x = H.c}

/-- The open half-space `H⁺ = {x | u · x > c}` (p.11). -/
def pos (H : Hyp d) : Set (E d) := {x | H.c < inner ℝ H.u x}

/-- The open half-space `H⁻ = {x | u · x < c}` (p.11). -/
def neg (H : Hyp d) : Set (E d) := {x | inner ℝ H.u x < H.c}

/-- The sign function `σ_H : ℝ^d → {−1, 0, +1}`: `+1` on `H⁺`, `−1` on `H⁻`, `0` on `H`
(§2.3, p.12). -/
noncomputable def sign (H : Hyp d) (x : E d) : ℝ :=
  if H.c < inner ℝ H.u x then 1 else if inner ℝ H.u x < H.c then -1 else 0

end Hyp

/-- The set of ordered pairs strictly separated by `H`,
`Sep(H) := (H⁺ × H⁻) ∪ (H⁻ × H⁺)` (§2.1, p.11). Separation is **strict**: both half-spaces are
open, so a pair with a point on `H` is not separated. -/
def Sep {d : ℕ} (H : Hyp d) : Set (E d × E d) := H.pos ×ˢ H.neg ∪ H.neg ×ˢ H.pos

/-- The strip `B(H, η) := {x ∈ ℝ^d | dist(x, H) ≤ η}`, with the Euclidean distance (§2.1, p.12). -/
def strip {d : ℕ} (H : Hyp d) (η : ℝ) : Set (E d) := {x | Metric.infDist x H.set ≤ η}

end SepMeasures


