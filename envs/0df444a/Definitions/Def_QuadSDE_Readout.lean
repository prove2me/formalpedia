-- Prove2me | Definitions.Def_QuadSDE_Readout
-- name    : QuadSDE_Readout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:28.020191+00:00
-- url     : https://prove2.me/theorems/a0f9dd6f-6626-4a41-a4b3-9165ff94f170
-- title:
--   Readout $\bar u$ and $|\psi_{\mathrm{out}}\rangle$ of the observables (58)
-- statement:
--   For an observable $u_0$, let $\bar u=\int u_0(\sqrt{\rho(T)}\,x)\mu(x)\,dx$ and let $|\psi_{\mathrm{out}}\rangle$ be the vector of Hermite coefficients of $u_0(\sqrt{\rho(T)}\,x)-\bar u$. Using $H_1(x)=x$ and $H_2(x)=(x^2-1)/\sqrt2$:
--
--   | $u_0(x)$ | $\bar u$ | $|\psi_{\mathrm{out}}\rangle$ |
--   |---|---|---|
--   | $x_i$ | $0$ | $\sqrt{\rho(T)}\,|e_i\rangle$ |
--   | $x_ix_j$, $i\ne j$ | $0$ | $\rho(T)\,|e_i+e_j\rangle$ |
--   | $x_i^2$ | $\rho(T)$ | $\sqrt2\,\rho(T)\,|2e_i\rangle$ |
--
--   Then $\mathbb E\,u_0(X(T))=\bar u+\langle\psi_{\mathrm{out}},\psi(T)\rangle$ (Eq. (59)).
--
--   **Formalization Note** $|\psi_{\mathrm{out}}\rangle$ is a finitely supported coefficient function on multi-indices; $e_i$ is the $i$-th unit multi-index.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.5, Eq. (58), p. 26

import Mathlib
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_Fock

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.5, Eq. (58), p. 26:
`ū = ∫ u₀(√ρ(T) x) μ(x) dx` for the three kinds of observable: `0` for `x_i`, `0` for `x_i x_j`
with `i ≠ j`, and `ρ(T)` for `x_i²`. -/
def ubar {N : ℕ} (obs : Observable N) (p q T : ℝ) : ℝ :=
  match obs with
  | .lin _ => 0
  | .quad i j => if i = j then rho p q T else 0

/-- Eq. (58), p. 26: `|ψ_out⟩`, the vector of Hermite coefficients of `u₀(√ρ(T) x) − ū`:
`√ρ(T) |e_i⟩` for `x_i`; `ρ(T) |e_i + e_j⟩` for `x_i x_j` with `i ≠ j`; `√2 ρ(T) |2e_i⟩` for
`x_i²`. -/
def psiOut {N : ℕ} (obs : Observable N) (p q T : ℝ) : MIdx N → ℂ :=
  match obs with
  | .lin i => fun m => if m = Pi.single i 1 then ((Real.sqrt (rho p q T) : ℝ) : ℂ) else 0
  | .quad i j =>
      if i = j then fun m => if m = Pi.single i 2 then ((Real.sqrt 2 * rho p q T : ℝ) : ℂ) else 0
      else fun m => if m = Pi.single i 1 + Pi.single j 1 then ((rho p q T : ℝ) : ℂ) else 0

end QuadSDE


