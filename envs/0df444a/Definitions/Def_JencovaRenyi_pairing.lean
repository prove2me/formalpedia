-- Prove2me | Definitions.Def_JencovaRenyi_pairing
-- name    : JencovaRenyi_pairing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:26.558731+00:00
-- url     : https://prove2.me/theorems/98067b22-c79e-4d0d-9db5-c3fa443ee050
-- title:
--   The duality $\langle h, k\rangle$ between $L_q(\mathcal M,\varphi)$ and $L_p(\mathcal M,\varphi)$
-- statement:
--   For $x\in\mathcal M$ and $k\in L_1(\mathcal M)$ the paper puts $\langle h_x, k\rangle = \langle k, h_x\rangle := \operatorname{Tr} kx = k(x)$. For $h\in L_q(\mathcal M,\varphi)$ and $k\in L_p(\mathcal M,\varphi)$, $1/p+1/q=1$, the extended pairing is the limit
--   $$
--   \langle h, k\rangle = \lim_{h_x\to h \text{ in } \|\cdot\|_{q,\varphi}} k(x).
--   $$
--   The pairing is bilinear (no complex conjugation). The first argument is the $L_q$ element, as in $\langle T_{q,\varphi}(h), h\rangle$ (p.6) and $\langle h_0, \Phi(h)\rangle$ in (17).
--
--   **Formalization Note** The limit is Mathlib's `Filter.limUnder` along the pull-back of the neighbourhoods of $0$ under $x\mapsto\|h-h_x\|_{q,\varphi}$. That this filter is proper and the limit exists for $h\in L_q$, $k\in L_p$, $1\le p<\infty$, is part of the milestone `JencovaRenyi.duality`; outside that range the value is unspecified and no statement uses it. The formula (7) through Haagerup's $L_p(\mathcal M)$ describes the same pairing.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, p.6 ("The duality $\langle k, h_x\rangle := \operatorname{Tr} kx$ … extends to a duality between $L_p(\mathcal M,\varphi)$ and $L_q(\mathcal M,\varphi)$")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_lpNorm

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The duality `⟨h, k⟩` between `L_q(M, φ)` and `L_p(M, φ)`, `1/p + 1/q = 1` (Jenčová,
arXiv:1609.08462v4, §2.2, p.6): the bilinear pairing `⟨h_x, k⟩ = ⟨k, h_x⟩ := Tr k x = k(x)` for
`x ∈ M`, `k ∈ L_1(M)`, extended to `h ∈ L_q(M, φ)` by continuity: `⟨h, k⟩` is the limit of
`k(x)` as `h_x → h` in `‖·‖_{q,φ}`.

**Formalization Note.** The limit is `limUnder` along the pull-back of the neighbourhoods of `0`
under `x ↦ ‖h − h_x‖_{q,φ}`. The milestone `duality` states that this filter is proper and
the limit exists for `h ∈ L_q(M, φ)`, `k ∈ L_p(M, φ)`; outside that range the value is
unspecified. The first argument is the `L_q` element, matching `⟨T_{q,φ}(h), h⟩` (p.6) and
`⟨h₀, Φ(h)⟩` (17), p.16. There is no complex conjugation: the pairing is bilinear. -/
noncomputable def pairing {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ : Predual A) (q : ℝ≥0∞) (h k : Predual A) : ℂ :=
  Filter.limUnder (Filter.comap (fun x : A => lpNorm S φ q (h - symmEmbed S φ x)) (nhds 0))
    (fun x : A => (k : A →L[ℂ] ℂ) x)

end JencovaRenyi


