-- Prove2me | Definitions.Def_GL2QFT_QFT
-- name    : GL2QFT_QFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:44.812184+00:00
-- url     : https://prove2.me/theorems/4f0c0eb9-d05e-4e2b-ad33-58ecd761e6cc
-- title:
--   The quantum Fourier transforms $\mathfrak F_G$ of $\mathrm{GL}_2(\mathbb F_q)$ and $\mathfrak F_B$ of $B$ in the paper's bases
-- statement:
--   The two Fourier transforms of §6, both instances of (22) with all phases equal to one.
--
--   1. For $G=\mathrm{GL}_2(\mathbb F_q)$, $|G|=(q^2-1)(q^2-q)$,
--   $$\mathfrak F_G|g\rangle=\sum_{\mu}\sqrt{\frac{d_\mu}{|G|}}\sum_{i,j}[R_\mu(g)]^i_j\,|\mu,i,j^*\rangle,$$
--   where $\mu$ runs over the labels of Table 2 and $R_\mu$ is written in the Gelfand–Tsetlin bases of §6.2.
--   2. For the Borel subgroup $B$ of (125), $|B|=q(q-1)^2$, $\mathfrak F_B$ is the same formula for the irreps $\chi_{\alpha,\beta}$ and $\rho_\gamma$ (in basis (108)), with columns indexed by the triples $(a,d,b)$, $g=\begin{pmatrix}1&b\\0&1\end{pmatrix}\begin{pmatrix}a&0\\0&d\end{pmatrix}$.
--
--   These are the unitaries that Theorem 6.1 and Theorem 6.13 implement.
--
--   **Formalization Note** A Fourier transform is determined only up to one phase per irrep and the choice of bases (Proposition 2.7). The mission fixes the paper's bases, so the target is a single explicit unitary. Its unitarity was checked numerically at $q=2,3,5,7$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Proposition 2.7 eq. (22) p.14; Theorem 6.1 p.34 (PDF p.35); Theorem 6.13 and (125) p.44 (PDF p.45)

import Definitions.Def_GL2QFT_Irreps

noncomputable section

open Classical

namespace GL2QFT

namespace FieldData

variable (D : FieldData)

/-- The output labels `(μ, i, j)` of the Fourier transform of `GL₂(F_q)`: an irrep label and a row
and column index of its Gelfand–Tsetlin basis ((20), p.14). -/
abbrev OutLabel : Type := Σ μ : D.Irr, D.Bas μ × D.Bas μ

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Proposition 2.7, eq. (22), p.14, for
`G = GL₂(F_q)` (Theorem 6.1, p.34): the quantum Fourier transform of `GL₂(F_q)`,
`F_G|g⟩ = Σ_μ √(d_μ/|G|) Σ_{i,j} [R_μ(g)]^i_j |μ, i, j*⟩`, with all phases equal to one, in the
paper's representatives and Gelfand–Tsetlin bases (`GL2QFT.FieldData.R`): models (87)–(100),
bases (108), (110)–(112), representative `α ≺ β` of `I_{α,β}`, orbit representative of `π_θ`.
`|G| = (q²−1)(q²−q)`, `d_μ ∈ {1, q, q+1, q−1}`. -/
def qftGL2 : Matrix D.OutLabel D.G ℂ := fourierMatrix D.R

/-- The output labels `(λ, i, j)` of the Fourier transform of `B`. -/
abbrev BOutLabel : Type := Σ ν : D.BIrr, D.BBas ν × D.BBas ν

/-- arXiv:2608.28573, Theorem 6.13 with (22), pp.14 and 44: the Fourier transform `F_B` of the Borel
subgroup `B = {(a b; 0 d)}` (125) in the representation bases fixed in §6.1–6.2 (characters
`χ_{α,β}` (87) and `ρ_γ` in the basis (108)): `F_B|g⟩ = Σ_λ √(d_λ/|B|) Σ_{i,j} [R_λ(g)]^i_j
|λ, i, j*⟩`, `|B| = q(q−1)²`. Its columns are indexed by the triples `(a, d, b)` with
`g = (1 b; 0 1)(a 0; 0 d)` (§6.4.2, p.43). -/
def qftB : Matrix D.BOutLabel D.BElt ℂ := fourierMatrix (fun ν x => D.RB ν (D.bmat x))

end FieldData

end GL2QFT


