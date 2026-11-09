-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Restriction
-- name    : ParityBarrier563_Trilinear_Restriction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:24.504945+00:00
-- url     : https://prove2.me/theorems/e7213217-5bde-49b0-8bdf-b1a2d0b0048b
-- title:
--   §2 — restrictions, live variables, restricted functions and the p-random law
-- statement:
--   A **restriction** of $V$ is a map $\rho:V\to\{0,1,*\}$. Its **live** set is $\mathrm{live}(\rho)=\rho^{-1}(*)$. For a function $\psi$ on $\{0,1\}^V$, the **restricted function** $\psi_\rho:\{0,1\}^{\mathrm{live}(\rho)}\to\mathbb R$ is obtained by fixing every coordinate outside $\mathrm{live}(\rho)$ to its value under $\rho$. For a restriction $\varphi$ of $V$ and a restriction $\rho$ of $\mathrm{live}(\varphi)$, the **composition** $\varphi\rho$ first fixes coordinates according to $\varphi$ and then the live ones according to $\rho$.
--
--   For $0<p\le1$, a **$p$-random restriction** of $V$ has independent coordinates, each equal to $*$ with probability $p$ and to $0$ and to $1$ with probability $(1-p)/2$ each. Thus restriction $\rho$ has probability
--
--   $$\Pr[\rho]=\prod_{v\in V}\begin{cases}p,&\rho(v)=*,\\ (1-p)/2,&\rho(v)\in\{0,1\}.\end{cases}$$
--
--   Expectations and probabilities over $\rho$ are the corresponding finite weighted sums.
--
--   Random restrictions drive both halves of the argument: the switching lemma and depth reduction on the circuit side, and the transfer from wide to narrow CNF tests on the correlation side.
--
--   **Formalization Note** `none` encodes $*$. The live set is the subtype $\{v\mid\rho(v)=*\}$, so $\psi_\rho$ is a function on its own cube; the iterated restriction $(\psi_\varphi)_\rho$ is the source's $\psi_{\varphi\rho}$.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, §2 Preliminaries, 'Random restrictions', printed p.10 (PDF p.12); composition, printed p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! §2, printed p.10 / PDF 12: restrictions `ρ ∈ {0,1,∗}^V`, live sets, restricted functions,
composition, and the `p`-random restriction law. -/

variable {V : Type}

/-- A restriction of `V`: `none` is the live value `∗`, `some c` fixes the coordinate to `c`. -/
abbrev Restriction (V : Type) := V → Option Bool

/-- `live(ρ) = ρ⁻¹(∗)`, as a type (the variables of the restricted function). -/
abbrev Live (ρ : Restriction V) := {v : V // ρ v = none}

/-- The point of `{0,1}^V` that agrees with `ρ` off `live(ρ)` and with `z` on `live(ρ)`. -/
def fill (ρ : Restriction V) (z : Live ρ → Bool) : V → Bool := fun v =>
  match h : ρ v with
  | none => z ⟨v, h⟩
  | some c => c

/-- The restricted function `ψ_ρ : {0,1}^{live(ρ)} → α`, obtained by fixing the coordinates
outside `live(ρ)` according to `ρ`. -/
def restrict {α : Type} (ρ : Restriction V) (ψ : (V → Bool) → α) : (Live ρ → Bool) → α :=
  fun z => ψ (fill ρ z)

/-- The composition `φρ` of a restriction `φ` of `V` and a restriction `ρ` of `live(φ)`:
it first fixes coordinates according to `φ` and then the live ones according to `ρ`. -/
def compose (φ : Restriction V) (ρ : Restriction (Live φ)) : Restriction V := fun v =>
  match h : φ v with
  | none => ρ ⟨v, h⟩
  | some c => some c

/-- The probability of `ρ` under the `p`-random restriction law: independent coordinates, each
`∗` with probability `p` and `0`, `1` with probability `(1 − p)/2` each (for `0 < p ≤ 1`). -/
noncomputable def restrictionWeight [Fintype V] (p : ℝ) (ρ : Restriction V) : ℝ :=
  ∏ v, (match ρ v with
    | none => p
    | some _ => (1 - p) / 2)

/-- `E_ρ[G(ρ)]` for a `p`-random restriction `ρ` of `V`. -/
noncomputable def restrExpect [Fintype V] [DecidableEq V] (p : ℝ) (G : Restriction V → ℝ) : ℝ :=
  ∑ ρ : Restriction V, restrictionWeight p ρ * G ρ

/-- `Pr_ρ[E(ρ)]` for a `p`-random restriction `ρ` of `V`. -/
noncomputable def restrProb [Fintype V] [DecidableEq V] (p : ℝ) (E : Restriction V → Prop) : ℝ := by
  classical exact restrExpect p (fun ρ => if E ρ then 1 else 0)

end ParityBarrier563.Trilinear


