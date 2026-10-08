-- Prove2me | Definitions.Def_ViscosityPPDE_Comparison_Standing
-- name    : ViscosityPPDE_Comparison_Standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:45.860926+00:00
-- url     : https://prove2.me/theorems/157db3cd-3ccc-49fb-9b14-05a15880071e
-- title:
--   Assumptions 4.2 and 4.4, and $u^0$ of (4.2)–(4.3) characterised by the BSDE
-- statement:
--   Let $f : \Lambda\times\mathbb R\times\mathbb R^d\to\mathbb R$ and $g : \Omega \to \mathbb R$.
--
--   **Assumption 4.2.** (i) $f$ is bounded, $\mathbb F$-progressively measurable, continuous in $t$, uniformly continuous in $\omega$, and uniformly Lipschitz continuous in $(y,z)$ with a Lipschitz constant $L_0 > 0$:
--   $$|f(t,\omega,y,z) - f(t,\omega,y',z')| \le L_0\big(|y-y'| + |z-z'|\big).$$
--   (ii) $g$ is bounded and uniformly continuous in $\omega$.
--
--   **Assumption 4.4.** There exists $\hat f : \hat\Lambda\times\mathbb R\times\mathbb R^d \to \mathbb R$ with (i) $\hat f = f$ on $\Lambda\times\mathbb R\times\mathbb R^d$; (ii) $\hat f$ bounded, $\hat f(\cdot,y,z) \in C^0(\hat\Lambda)$ for every fixed $(y,z)$, and $\hat f$ uniformly Lipschitz continuous in $(y,z)$.
--
--   **The function $u^0$.** For $(t,\omega) \in \Lambda$ the BSDE on $[t,T]$
--   $$Y^{0,t,\omega}_s = g^{t,\omega}(B^t_\cdot) + \int_s^T f^{t,\omega}(r,B^t_\cdot,Y^{0,t,\omega}_r,Z^{0,t,\omega}_r)\,dr - \int_s^T Z^{0,t,\omega}_r\,dB^t_r,\quad P^t_0\text{-a.s.} \qquad (4.2)$$
--   has a unique solution (Pardoux–Peng), $Y^{0,t,\omega}_t$ is a constant, and $u^0(t,\omega) := Y^{0,t,\omega}_t$ (4.3). The predicate $\mathrm{IsU0}(u)$ says: for every $(t,\omega)\in\Lambda$ some solution $(Y,Z)$ of (4.2) has $Y_t = u(t,\omega)$ $P^t_0$-a.s.
--
--   These are the standing data of the main results: Theorem 4.3 and Proposition 5.4 assume 4.2, Theorem 4.6 and Theorem 6.1 assume 4.2 and 4.4.
--
--   **Formalization Note** The three readings of Assumption 4.2(i): "continuous in $t$" is for each fixed $(\omega,y,z)$ on $[0,T]$; "uniformly continuous in $\omega$" is one modulus for $\|\cdot\|_T$, uniform in $(t,y,z)$ (the proof of Proposition 5.4 uses it at random $(y,z)$); the Lipschitz bound uses $|y-y'|+|z-z'|$ with the Euclidean $|z|$. Progressive measurability is required for each fixed $(y,z)$. $u^0$ is characterised, not constructed: the BSDE is Peng's `SolvesBSDE` (platform definition `Peng1990.SMP.Stochastic`) for $\mathbb F^t$ and $P^t_0$, with scalar $Y$ and generator $0$ before $t$. By Pardoux–Peng existence and uniqueness exactly one $u$ satisfies $\mathrm{IsU0}$, so the statements quantifying over such $u$ are not vacuous; that existence is not an item of this mission. The sorry-free check `u⁰(T,ω) = g(ω)` is proved from the definition.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Assumption 4.2, p. 15; (4.2), (4.3), Assumption 4.4, p. 16

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ViscosityPPDE_Comparison_Calculus

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

variable {d : ℕ} {T : ℝ≥0}

/-- Assumption 4.2. (i) `f` is bounded, `𝔽`-progressively measurable, continuous in `t`, uniformly
continuous in `ω` (one modulus, uniform in `(t, y, z)`, for `‖·‖_T`), and uniformly Lipschitz in
`(y, z)` with constant `L₀ > 0`: `|f(t,ω,y,z) − f(t,ω,y',z')| ≤ L₀ (|y − y'| + |z − z'|)`.
(ii) `g` is bounded and uniformly continuous in `ω` for `‖·‖_T`. -/
structure Assumption42 (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ)
    (L0 : ℝ) : Prop where
  f_bdd : ∃ C, ∀ t ω y z, t ≤ T → |f t ω y z| ≤ C
  f_prog : ∀ y z, IsProg T 0 (fun s ω => f s ω y z)
  f_cont_t : ∀ ω y z, ContinuousOn (fun s => f s ω y z) (Set.Icc 0 T)
  f_unif_ω : ∀ ε > 0, ∃ δ > 0, ∀ t (ω ω' : Omega d T 0) y z, t ≤ T →
    SupNormLt T (ω.1 - ω'.1) δ → |f t ω y z - f t ω' y z| < ε
  L0_pos : 0 < L0
  f_lip : ∀ t ω y y' z z', t ≤ T → |f t ω y z - f t ω y' z'| ≤ L0 * (|y - y'| + ‖z - z'‖)
  g_bdd : ∃ C, ∀ ω, |g ω| ≤ C
  g_unif : ∀ ε > 0, ∃ δ > 0, ∀ ω ω' : Omega d T 0, SupNormLt T (ω.1 - ω'.1) δ → |g ω - g ω'| < ε

/-- Assumption 4.4: `f̂ : Λ̂ × ℝ × ℝ^d → ℝ` with (i) `f̂ = f` on `Λ × ℝ × ℝ^d`; (ii) `f̂` bounded,
`f̂(·, y, z) ∈ C^0(Λ̂)` for each fixed `(y, z)`, and `f̂` uniformly Lipschitz in `(y, z)`. -/
structure Assumption44 (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (fhat : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ → Rd d → ℝ) : Prop where
  ext : ∀ t (ω : Omega d T 0) y z, t ≤ T → fhat t ω.1 y z = f t ω y z
  bdd : ∃ C, ∀ t ω y z, t ≤ T → ω ∈ OmegaHatSet d T 0 → |fhat t ω y z| ≤ C
  cont : ∀ y z, IsC0Hat T 0 (fun s ω => fhat s ω y z)
  lip : ∃ L, ∀ t ω y y' z z', t ≤ T → ω ∈ OmegaHatSet d T 0 →
    |fhat t ω y z - fhat t ω y' z'| ≤ L * (|y - y'| + ‖z - z'‖)

/-- `u` is `u⁰` of (4.2)–(4.3): for every `(t, ω) ∈ Λ` there is a solution `(Y, Z)` of the BSDE
`Y_s = g^{t,ω}(B^t) + ∫_s^T f^{t,ω}(r, B^t, Y_r, Z_r) dr − ∫_s^T Z_r dB^t_r` under `P^t_0` for the
filtration `𝔽^t` (Peng's `SolvesBSDE`, scalar `Y`, generator `0` before `t`), with
`Y_t = u(t, ω)` `P^t_0`-a.s. (`Y_t` is `𝓕^t_t`-measurable, hence constant). -/
def IsU0 (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (g : Omega d T 0 → ℝ) (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  ∀ t (ω : Omega d T 0), t ≤ T →
    ∃ (Y : ℝ≥0 → Omega d T t → Unit → ℝ) (Z : Fin d → ℝ≥0 → Omega d T t → Unit → ℝ),
      Peng1990.SMP.SolvesBSDE (filt d T t) (Pt P0 t) T (fun s ω' j => ω'.1 s j)
        (fun ω' _ => g (concat ω t ω'))
        (fun s ω' y z _ => if t ≤ s then
          f s (concat ω t ω') (y ()) (WithLp.toLp 2 (fun j => z j ())) else 0)
        Y Z ∧
      ∀ᵐ ω' ∂(Pt P0 t), Y t ω' () = u t ω

end ViscosityPPDE.Comparison


