-- Prove2me | Definitions.Def_SYKLearn_Direction
-- name    : SYKLearn_Direction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:33.368766+00:00
-- url     : https://prove2.me/theorems/e7101792-443e-42b8-86f9-44a84b6afe1e
-- title:
--   The direction matrix $(M_\beta)_{S,I}=-\mathrm{Tr}[\rho_{\beta,g}[\Gamma_S,\Gamma_I]]$ and the annealed Gibbs components $\bar\rho_k$
-- statement:
--   Let $\rho_{\beta,g}=e^{-\beta H_g}/\mathrm{Tr}[e^{-\beta H_g}]$ be the Gibbs state at inverse temperature $\beta$ (normalized trace; the physical state is $2^{-n/2}\rho_{\beta,g}=e^{-\beta H_g}/\mathrm{tr}[e^{-\beta H_g}]$).
--
--   1. The **direction matrix** has rows indexed by $6$-sets $S$ and columns by $4$-sets $I$:
--   $$(M_\beta)_{S,I}=-\mathrm{Tr}\big[\rho_{\beta,g}[\Gamma_S,\Gamma_I]\big].$$
--   Since $\rho_{\beta,g}$ commutes with $H_g$, the coupling vector satisfies $M_\beta g=0$.
--   2. The **annealed Gibbs state** $\bar\rho=e^{-\beta H_g}/\mathbb E_g\mathrm{Tr}[e^{-\beta H_g}]$ has degree-$k$ component
--   $$\bar\rho_k=\frac{1}{\mathbb E_g\mathrm{Tr}[e^{-\beta H_g}]}\sum_{|S|=k}\mathrm{Tr}[e^{-\beta H_g}\Gamma_S]\,\Gamma_S,$$
--   viewed as a vector of $\mathbb M_k$; $\bar\rho_{4,8}=\bar\rho_4+\bar\rho_8$.
--
--   The matrix $M_\beta$ is what the learner estimates from Gibbs samples; its gap on $g^\perp$ (Lemma 3.2) is proved through the annealed components.
--
--   **Formalization Note** The Gibbs state is the published physical `SYKFastMix.FastMixing.gibbs` (ordinary trace), and $\mathrm{Tr}[\rho_\beta X]=\mathrm{tr}[\texttt{gibbs}\cdot X]$. The entries of $M_\beta$ are real (the commutator of the anti-Hermitian $\Gamma_S$ and the Hermitian $\Gamma_I$ is Hermitian); the real part is taken. The annealed components are used for $k\in\{4,8\}$, where $\mathrm{Tr}[e^{-\beta H}\Gamma_S]$ is real. The expectation is over the coupling law of the model.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), (4), p.4; (28), p.18; (29) and the annealed state, p.19

import Mathlib
import Definitions.Def_SYKLearn_Basic

noncomputable section
open Matrix MeasureTheory

namespace SYKLearn

/-!
# The direction matrix `M_β` and the annealed Gibbs components `ρ_k`

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), (4), p.4; (28), p.18; annealed state and (29), p.19.

**Formalization Note.**
* The Gibbs state is the published `SYKFastMix.FastMixing.gibbs H β = e^{−βH}/tr[e^{−βH}]`, the
  paper's **physical** state `2^{−n/2} ρ_β` (ordinary trace). For any `X`,
  `Tr[ρ_β X] = tr[gibbs H β · X]`, since `ρ_β = 2^{n/2} · gibbs H β` and `Tr = 2^{−n/2} tr`.
* `Mmat β Q w` is `(M_β)_{S,I} = −Tr[ρ_{β,g}[Γ_S, Γ_I]]` for `|S| = 6`, `|I| = 4`, `g = w`. The
  commutator of the anti-Hermitian `Γ_S` and the Hermitian `Γ_I` is Hermitian, so the trace is
  real; the entry is its real part.
* `annealedZ β Q = E_g Tr[e^{−βH_g}]` (normalized trace, expectation over `disorderLaw Q`).
* `rhoK β Q k w` is the annealed degree-`k` component
  `ρ_k = (E_g Tr[e^{−βH_g}])^{−1} Σ_{|S|=k} Tr[e^{−βH_g}Γ_S] Γ_S` (p.19), as the vector of its
  coefficients in `M_k`. It is used for `k ∈ {4, 8}`, where `Γ_S` is Hermitian and
  `Tr[e^{−βH}Γ_S]` is real; the real part is taken. `rho48 = ρ_4 + ρ_8 = ρ_{4,8}`.
-/

open SYKFastMix.FastMixing

/-- `(M_β)_{S,I} = −Tr[ρ_{β,g}[Γ_S, Γ_I]]`, `|S| = 6`, `|I| = 4` ((4), p.4; (28), p.18). -/
def Mmat {N : ℕ} (β : ℝ) (Q : Model N) (w : Disorder N) :
    Matrix (SYKEdge.KSet N 6) (SYKEdge.KSet N 4) ℝ :=
  fun S I => -(Matrix.trace (gibbs (hamiltonian Q w) β *
    (rawString Q S.1 * rawString Q I.1 - rawString Q I.1 * rawString Q S.1))).re

/-- The annealed partition function `E_g Tr[e^{−βH_g}]` (p.19). -/
def annealedZ {N : ℕ} (β : ℝ) (Q : Model N) : ℝ :=
  ∫ w, (SYKEdge.ntr (mexp ((-β : ℂ) • hamiltonian Q w))).re ∂(disorderLaw Q)

/-- The annealed degree-`k` component `ρ_k` of the Gibbs state, as a vector of `M_k` (p.19). -/
def rhoK {N : ℕ} (β : ℝ) (Q : Model N) (k : ℕ) (w : Disorder N) : Ext N :=
  fun S => if S.card = k then
    (SYKEdge.ntr (mexp ((-β : ℂ) • hamiltonian Q w) * rawString Q S)).re / annealedZ β Q
  else 0

/-- `ρ_{4,8} = ρ_4 + ρ_8` ((29), p.19). -/
def rho48 {N : ℕ} (β : ℝ) (Q : Model N) (w : Disorder N) : Ext N :=
  rhoK β Q 4 w + rhoK β Q 8 w

end SYKLearn


