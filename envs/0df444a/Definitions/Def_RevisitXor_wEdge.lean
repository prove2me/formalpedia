-- Prove2me | Definitions.Def_RevisitXor_wEdge
-- name    : RevisitXor_wEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:06.839317+00:00
-- url     : https://prove2.me/theorems/ed675443-16a8-4db3-8d92-4c3da2db8a50
-- title:
--   Edge weights $w(y\to z)$ and $w(\{y,z\})$
-- statement:
--   Fix $h:[2]^m\times[2]^m\to[2]$ (a function on $[2]^n$, $n=2m$, read on the pair $(x,y)$). For $y,z\in[2]^m$ the **directed weight**
--
--   $$w(y\to z)=\mathbb E_{x\in[2]^m}(-1)^{x\cdot z+h(x,y)}$$
--
--   is the contribution to the correlation of $h$ with $f_\pi$ from the column $y$ when $\pi(y)=z$. The **undirected weight** of an edge $\{y,z\}$ with $y\ne z$ is
--
--   $$w(\{y,z\})=w(y\to z)+w(z\to y),$$
--
--   and $w(\{y\})=0$ on a loop, although $w(y\to y)$ may be nonzero.
--
--   **Formalization Note** `wDir h y z` is $w(y\to z)$; `wEdge h` is $w$ on unordered pairs `Sym2 ([2]^m)`, zero on the diagonal.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6

import Mathlib
import Definitions.Def_RevisitXor_corr

namespace RevisitXor

/-- **Directed weight `w(y → z)`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission
(manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6: "w(y → z) := E_x(−1)^{x.z+h(x,y)} be
the contribution to the correlation when y is fixed and π(y) = z."

**Formalization Note.** `h : [2]^m × [2]^m → ZMod 2` is the fixed function `h : [2]^n → [2]` with
`n = 2m`, read on the split `(x, y)`; `E_x` is the uniform average over `x ∈ [2]^m`. -/
noncomputable def wDir {m : ℕ} (h : Cube m × Cube m → ZMod 2) (y z : Cube m) : ℝ :=
  (Fintype.card (Cube m) : ℝ)⁻¹ * ∑ x : Cube m, sgn (x ⬝ᵥ z + h (x, y))

/-- **Undirected weight `w({y, z})`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission
(manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6: "w({y, z}) := w(y → z) + w(z → y) be
the undirected contribution along edge {y, z}. We let w({y}) := 0 though note that w(y → y) may not
be zero."

**Formalization Note.** Edges are unordered pairs `Sym2 ([2]^m)`; the diagonal `{y} = s(y, y)` has
weight `0`. -/
noncomputable def wEdge {m : ℕ} (h : Cube m × Cube m → ZMod 2) : Sym2 (Cube m) → ℝ :=
  Sym2.lift ⟨fun y z => if y = z then 0 else wDir h y z + wDir h z y, fun y z => by
    by_cases hyz : y = z
    · simp [hyz]
    · simp [hyz, Ne.symm hyz, add_comm]⟩

end RevisitXor


