-- Prove2me | Definitions.Def_StreamColour_SampledPalette
-- name    : StreamColour_SampledPalette
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:00.169704+00:00
-- url     : https://prove2.me/theorems/14c910bd-40cc-4a9c-8e57-538227975152
-- title:
--   §§4.2–4.3 — the lists $L(v)$ and the sampled palettes $Q_v(D)$
-- statement:
--   For a proper $q$-colouring $\varphi_K$ of $G[K]$, $L_0(v)$ is the set of colours of $[q]$ not used by $\varphi_K$ on $N_G(v)\cap K$, and $L(v)$ consists of the smallest $\min\{|L_0(v)|,d_v+1\}$ colours of $L_0(v)$.
--
--   Each vertex samples a priority $\theta_v$, uniform on $\{0,1/g,\dots,(g-1)/g\}$, with $g$ the smallest power of two at least $n^3$, and two ordered arrays of $p_{\max}=\lceil C_{\mathrm{A,pal}}q\ell/h\rceil$ independent uniform colours, repetitions kept. With
--
--   $$a(D)=\lceil C_{\mathrm{A,pal}}q\ell/D\rceil,\qquad b_v(D)=\Bigl\lceil\frac{C_{\mathrm{A,pal}}q\ell}{h+D\theta_v}\Bigr\rceil,$$
--
--   $Q_v(D)$ is the set of colours in the first $a(D)$ entries of the first array or the first $b_v(D)$ entries of the second. $D_v$ is the power of two with $D_v\le d_v+1<2D_v$.
--
--   **Formalization Note** Colours are `Fin q`. A prefix counts entries, including repeated ones.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §4.2, pp.26, 28 (PDF 28, 30); §4.3, p.37 (PDF 39)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_Reduction

namespace StreamColour

/-! # Lists and sampled palettes of Algorithm A

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §4.2, p.26 (PDF 28):
`L₀(v)` is the set of colours of `[q]` not used by `φ_K` on `N_G(v) ∩ K`, and `L(v)` consists of its
smallest `min{|L₀(v)|, d_v + 1}` colours. §4.3, p.37 (PDF 39): `p_max = ⌈C_{A,pal} q ℓ / h⌉`,
`a(D) = ⌈C_{A,pal} q ℓ / D⌉`, `b_v(D) = ⌈C_{A,pal} q ℓ / (h + D θ_v)⌉`, and `Q_v(D)`, the colours in the
first `a(D)` entries of the first array or the first `b_v(D)` of the second. §4.2, p.28 (PDF 30): `θ_v` is
uniform on `{0, 1/g, …, (g−1)/g}`, where `g` is the smallest power of two at least `n³`.

**Formalization Note.** Colours are `Fin q`. Arrays are functions of `Fin p_max`, so entries may repeat
and a prefix counts entries. All prefix lengths are real ceilings; `h ≥ 1` in every use, so no denominator
is `0`. `D_v = 2^⌊log₂(d_v + 1)⌋` is the power of two with `D_v ≤ d_v + 1 < 2 D_v`. -/

variable {n q : ℕ}

/-- `g`, the smallest power of two at least `n³`. -/
def gridSize (n : ℕ) : ℕ := 2 ^ Nat.clog 2 (n ^ 3)

/-- The priority `θ = i / g`. -/
noncomputable def theta (n : ℕ) (i : Fin (gridSize n)) : ℝ := (i.val : ℝ) / (gridSize n : ℝ)

/-- `L₀(v)`: the colours not used by `φ` on the removed neighbours of `v`. -/
def listL0 (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (φ : Fin n → Fin q)
    (v : Fin n) : Finset (Fin q) :=
  Finset.univ.filter fun c => ∀ u, u ∉ U → G.Adj v u → φ u ≠ c

/-- `L(v)`: the smallest `min{|L₀(v)|, d_v + 1}` colours of `L₀(v)`. -/
def listL (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (φ : Fin n → Fin q)
    (v : Fin n) : Finset (Fin q) :=
  (((List.finRange q).filter (· ∈ listL0 G U φ v)).take (liveDeg G U v + 1)).toFinset

/-- `p_max = ⌈C_{A,pal} q ℓ / h⌉`. -/
noncomputable def pMax (Cp : ℝ) (q n h : ℕ) : ℕ := ⌈Cp * (q : ℝ) * (ell n : ℝ) / (h : ℝ)⌉₊

/-- `a(D) = ⌈C_{A,pal} q ℓ / D⌉`. -/
noncomputable def prefixA (Cp : ℝ) (q n D : ℕ) : ℕ := ⌈Cp * (q : ℝ) * (ell n : ℝ) / (D : ℝ)⌉₊

/-- `b_v(D) = ⌈C_{A,pal} q ℓ / (h + D θ_v)⌉`. -/
noncomputable def prefixB (Cp : ℝ) (q n h D : ℕ) (θ : ℝ) : ℕ :=
  ⌈Cp * (q : ℝ) * (ell n : ℝ) / ((h : ℝ) + (D : ℝ) * θ)⌉₊

/-- The colours in the first `a` entries of `A₁` or the first `b` entries of `A₂`. -/
def prefixColours {p : ℕ} (A₁ A₂ : Fin p → Fin q) (a b : ℕ) : Finset (Fin q) :=
  ((Finset.univ.filter fun i : Fin p => i.val < a).image A₁) ∪
    ((Finset.univ.filter fun i : Fin p => i.val < b).image A₂)

/-- `D_v`, the power of two with `D_v ≤ d + 1 < 2 D_v`. -/
def powerScale (d : ℕ) : ℕ := 2 ^ Nat.log 2 (d + 1)

end StreamColour


