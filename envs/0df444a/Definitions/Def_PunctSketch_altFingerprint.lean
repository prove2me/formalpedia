-- Prove2me | Definitions.Def_PunctSketch_altFingerprint
-- name    : PunctSketch_altFingerprint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:27.588839+00:00
-- url     : https://prove2.me/theorems/db6802f5-b473-4352-9eed-53e1aa83ed5f
-- title:
--   The alternate fingerprint (8)
-- statement:
--   For a matrix $\Phi$ of field elements, $f(v)_t=\sum_{u\in N(v)}\mathrm{sgn}(v-u)\Phi_{t,u}$. For a vector $\boldsymbol p$, $z(v)=\boldsymbol p^{\mathsf T}\Phi_v$, and the artificial sketch in the coordinate of $\boldsymbol p=\boldsymbol p_t$ is
--   $$\tilde f_F(v)_t=z_t(v)\,\boldsymbol p_t^{\mathsf T}f(v).$$
--   The fingerprint of a purported edge set $E$ is $\sum_{v\in C}\sum_{u\notin C\cup F,\ \{v,u\}\in E}\mathrm{sgn}(v-u)z_t(v)z_t(u)$.
--
--   **Formalization Note** The page prints $z_j(v)$ in (8), a misprint for $z_t(v)$: the proof of Lemma 5.4 expands $z_t(v)$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, pp.19–20 (PDF pp.20–21), eq. (8), (9)

import Mathlib
import Definitions.Def_PunctSketch_sgn

namespace PunctSketch

open Classical in
/-- **The alternate fingerprint.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19: `f(v)_t = Σ_{u∈N(v)} sgn(v − u) Φ_{t,u}` for a
matrix `Φ` of field elements with `c + k` rows. -/
noncomputable def altFingerprint {n D Q : ℕ} (G : SimpleGraph (Fin n))
    (Φ : Fin D → Fin n → ZMod Q) (v : Fin n) (t : Fin D) : ZMod Q :=
  ∑ u ∈ Finset.univ.filter (G.Adj v), ((sgn v u : ℤ) : ZMod Q) * Φ t u

/-- `z(v) = 𝒑ᵀ Φ_v`, with `Φ_v` the `v`-th column of `Φ`. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19. -/
def altZ {n D Q : ℕ} (Φ : Fin D → Fin n → ZMod Q) (p : Fin D → ZMod Q) (v : Fin n) : ZMod Q :=
  ∑ i, p i * Φ i v

/-- **The artificial alternate sketch (8) in one coordinate.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19, eq. (8):
`f̃_F(v)_t = z_t(v) 𝒑_tᵀ f(v)`, for the kernel vector `p = 𝒑_t`.

**Formalization Note.** The page prints `z_j(v)` in (8), a misprint for `z_t(v)`; the proof of Lemma
5.4 expands `z_t(v)`. -/
noncomputable def altPunctured {n D Q : ℕ} (G : SimpleGraph (Fin n))
    (Φ : Fin D → Fin n → ZMod Q) (p : Fin D → ZMod Q) (v : Fin n) : ZMod Q :=
  altZ Φ p v * ∑ i, p i * altFingerprint G Φ v i

open Classical in
/-- The fingerprint of a purported edge set `E` in the alternate construction: the right side of (9),
one coordinate, with `z = altZ Φ p`. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.20. -/
noncomputable def altBoundaryFp {n D Q : ℕ} (Φ : Fin D → Fin n → ZMod Q) (p : Fin D → ZMod Q)
    (F C : Finset (Fin n)) (E : Set (Sym2 (Fin n))) : ZMod Q :=
  ∑ v ∈ C, ∑ u ∈ Finset.univ.filter (fun u => u ∉ C ∧ u ∉ F ∧ s(v, u) ∈ E),
    ((sgn v u : ℤ) : ZMod Q) * altZ Φ p v * altZ Φ p u

end PunctSketch


