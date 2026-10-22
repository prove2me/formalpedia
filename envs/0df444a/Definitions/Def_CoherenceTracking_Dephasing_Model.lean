-- Prove2me | Definitions.Def_CoherenceTracking_Dephasing_Model
-- name    : CoherenceTracking_Dephasing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:35.61899+00:00
-- url     : https://prove2.me/theorems/beb455b2-a725-45fa-90a9-2c7e4c0f0aa2
-- title:
--   §II.B, §III.A–B, eqs. (7)–(13), (30)–(32), (37)–(38), (41)–(42) — controlled pure-dephasing qubit: states, Bloch vector, coherence, master equation, breakdown time, tracking fields
-- statement:
--   This module fixes the model of a single qubit under pure dephasing and Hamiltonian control, following Lidar and Schneider, *Stabilizing qubit coherence via tracking-control*.
--
--   1. **Operators and Pauli matrices.** Qubit operators are complex $2\times 2$ matrices in the basis $|0\rangle,|1\rangle$. The Pauli matrices are
--   $$\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   2. **Qubit states** (p. 3). A density matrix $\rho=(\rho_{ij})$ satisfies $\operatorname{Tr}\rho=1$, $\rho_{10}=\rho_{01}^*$ (Hermiticity) and $\operatorname{Tr}(\rho^2)\le 1$.
--   3. **Bloch vector and coherence** (eqs. (9), (11)). The Bloch vector of $\rho$ is $\vec v=(v_x,v_y,v_z)$ with $v_\alpha=\operatorname{Re}\operatorname{Tr}(\rho\sigma_\alpha)$; conversely $\vec v$ determines the matrix $\tfrac12(I+\vec v\cdot\vec\sigma)$. The **coherence** is the squared radius in the $x$–$y$ plane,
--   $$c=v_x^2+v_y^2 .$$
--   4. **Controlled dynamics** (eqs. (13), (32), (30)). For controls $\omega_0,\omega_1,\omega_2$ and $\hbar>0$, the Hamiltonian is $H=\tfrac{\hbar}{2}(\omega_0\sigma_z+\omega_1\sigma_x-\omega_2\sigma_y)$ and the master equation with dephasing rate $\gamma$ is
--   $$\frac{\partial\rho}{\partial t}=-\frac{i}{\hbar}[H,\rho]+\frac{\gamma}{2}\left(\sigma_z\rho\sigma_z-\rho\right).$$
--   The Bloch equations are $\dot{\vec v}=M(t)\vec v$ with
--   $$M(t)=\begin{pmatrix}-\gamma&-\omega_0(t)&-\omega_2(t)\\ \omega_0(t)&-\gamma&-\omega_1(t)\\ \omega_2(t)&\omega_1(t)&0\end{pmatrix}.$$
--   A trajectory *solves* either equation on $[0,T)$ if it is continuous on $[0,T)$ and has the prescribed derivative at every $t\in(0,T)$.
--   5. **Breakdown time and tracking solution** (eqs. (37), (38), (41), (42)). For an initial Bloch vector $\vec v(0)$ with coherence $c$, set $t_b=v_z(0)^2/(2\gamma c)$, and with $s=\operatorname{sign}v_z(0)$ and $R(t)=v_z(0)^2-2\gamma c t$,
--   $$\vec v(t)=\bigl(v_x(0),\,v_y(0),\,s\sqrt{R(t)}\bigr),\qquad \omega_2(t)=s\,\frac{-\gamma v_x(0)-\omega_0(t)v_y(0)}{\sqrt{R(t)}},\qquad \omega_1(t)=s\,\frac{-\gamma v_y(0)+\omega_0(t)v_x(0)}{\sqrt{R(t)}},$$
--   with $\omega_0$ an arbitrary function. The tracked state is $\tfrac12(I+\vec v(t)\cdot\vec\sigma)$.
--
--   These are the objects every statement of the mission is about: the goal says that the coherence can be kept exactly constant until $t_b$ and no longer, and that the fields above diverge at $t_b$.
--
--   **Formalization Note** The Pauli matrices are the published `MIPRE.LCS.Pauli.X/Y/Z`, indexed $0,1,2$ for $x,y,z$; Bloch vectors are `Fin 3 → ℝ` in the order $x,y,z$, controls are `Fin 3 → ℝ` with index $0,1,2$ for $\omega_0,\omega_1,\omega_2$ (note $\omega_0$ multiplies $\sigma_z$). The paper's eq. (8) prints $v_\alpha=\tfrac12\operatorname{Tr}(\rho\sigma_\alpha)$; that factor $\tfrac12$ contradicts eq. (9), and the definition follows (9). The real part makes the Bloch vector real-valued for every matrix; on Hermitian matrices it is the trace itself. Square roots and divisions are Lean's total functions (`√x = 0` for `x < 0`, `x/0 = 0`); every statement about $t_b$, $\vec v(t)$ and the fields restricts to the range where they are the paper's. The sign $(\pm)$ of (37), (41), (42) is `Real.sign (v_z(0))`. Controls are arbitrary real functions; no measurability or continuity is imposed.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, pp. 3–6, §II.B eqs. (7)–(11), §III.A eq. (13), §III.B eqs. (30)–(32), §III.B.2 eqs. (37)–(38), (41)–(42)

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli

namespace CoherenceTracking.Dephasing

open Matrix Complex

/-- Qubit operators: `2 × 2` complex matrices, index `0` = `|0⟩`, `1` = `|1⟩`, as in (7). -/
abbrev Qmat := Matrix (Fin 2) (Fin 2) ℂ

/-- Bloch vectors, components in the order `x, y, z`. -/
abbrev BVec := Fin 3 → ℝ

/-- The Pauli matrices `σ_x, σ_y, σ_z`, indexed `0, 1, 2`. -/
def pauli : Fin 3 → Qmat := ![MIPRE.LCS.Pauli.X, MIPRE.LCS.Pauli.Y, MIPRE.LCS.Pauli.Z]

/-- p. 3: a qubit density matrix satisfies `ρ₁₀ = ρ₀₁*` (Hermitian), `Tr ρ = 1`, `Tr ρ² ≤ 1`. -/
def IsQubitState (ρ : Qmat) : Prop :=
  ρᴴ = ρ ∧ ρ.trace = 1 ∧ (ρ * ρ).trace.re ≤ 1

/-- The Bloch vector `v_α = Tr(ρ σ_α)` (the inverse of (9)). -/
noncomputable def blochVec (ρ : Qmat) : BVec := fun α => (ρ * pauli α).trace.re

/-- (9): `ρ = ½ (I + v · σ)`. -/
noncomputable def blochState (v : BVec) : Qmat :=
  (1 / 2 : ℂ) • (1 + ∑ α, ((v α : ℝ) : ℂ) • pauli α)

/-- (11): the coherence `c = v_x² + v_y²`. -/
noncomputable def coherence (ρ : Qmat) : ℝ := blochVec ρ 0 ^ 2 + blochVec ρ 1 ^ 2

/-- (13): `H = (ℏ/2)(ω₀ σ_z + ω₁ σ_x − ω₂ σ_y)`, with `ω 0 = ω₀`, `ω 1 = ω₁`, `ω 2 = ω₂`. -/
noncomputable def hamiltonian (hbar : ℝ) (ω : Fin 3 → ℝ) : Qmat :=
  ((hbar / 2 : ℝ) : ℂ) •
    (((ω 0 : ℝ) : ℂ) • pauli 2 + ((ω 1 : ℝ) : ℂ) • pauli 0 - ((ω 2 : ℝ) : ℂ) • pauli 1)

/-- Right-hand side of (32): `−(i/ℏ)[H, ρ] + (γ/2)(σ_z ρ σ_z − ρ)`. -/
noncomputable def masterRHS (hbar γ : ℝ) (ω : Fin 3 → ℝ) (ρ : Qmat) : Qmat :=
  (-I / (hbar : ℂ)) • (hamiltonian hbar ω * ρ - ρ * hamiltonian hbar ω)
    + ((γ / 2 : ℝ) : ℂ) • (pauli 2 * ρ * pauli 2 - ρ)

/-- The matrix of the Bloch equations (30). -/
def blochMatrix (γ : ℝ) (ω : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-γ, -ω 0, -ω 2; ω 0, -γ, -ω 1; ω 2, ω 1, 0]

/-- `ρ` solves the master equation (32) on `[0, T)` with controls `ω`: continuous on `[0, T)`,
differentiable with derivative (32) at every `t ∈ (0, T)`. -/
def SolvesMaster (hbar γ : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat) (T : ℝ) : Prop :=
  ContinuousOn ρ (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt ρ (masterRHS hbar γ (ω t) (ρ t)) t

/-- `v` solves the Bloch equations (30) on `[0, T)` with controls `ω`. -/
def SolvesBloch (γ : ℝ) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ) : Prop :=
  ContinuousOn v (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt v ((blochMatrix γ (ω t)).mulVec (v t)) t

/-- The coherence `v_x² + v_y²` of a Bloch vector. -/
def initCoherence (v0 : BVec) : ℝ := v0 0 ^ 2 + v0 1 ^ 2

/-- (38): the breakdown time `t_b = v_z(0)² / (2 γ c)`. -/
noncomputable def breakdownTime (γ : ℝ) (v0 : BVec) : ℝ :=
  v0 2 ^ 2 / (2 * γ * initCoherence v0)

/-- (37) with `(±) = sign v_z(0)` and `v_x, v_y` frozen at their initial values. -/
noncomputable def trackedBloch (γ : ℝ) (v0 : BVec) (t : ℝ) : BVec :=
  ![v0 0, v0 1, Real.sign (v0 2) * √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)]

/-- (41)–(42) with `(±) = sign v_z(0)`; component `0` is the free field `ω₀`,
component `1` is `ω₁` (42), component `2` is `ω₂` (41). -/
noncomputable def trackingFields (γ : ℝ) (v0 : BVec) (ω0 : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![ω0 t,
    Real.sign (v0 2) * (-γ * v0 1 + ω0 t * v0 0) / √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t),
    Real.sign (v0 2) * (-γ * v0 0 - ω0 t * v0 1) / √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)]

/-- The tracked density matrix `½ (I + v(t) · σ)` with `v(t)` from (37). -/
noncomputable def trackedState (γ : ℝ) (v0 : BVec) (t : ℝ) : Qmat :=
  blochState (trackedBloch γ v0 t)

end CoherenceTracking.Dephasing


