-- Prove2me | Definitions.Def_MayersQKD_testEffect
-- name    : MayersQKD_testEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:44.116198+00:00
-- url     : https://prove2.me/theorems/b5029911-ca17-455e-82db-5eb4d7ebf8e0
-- title:
--   The effect $\Pi_{(pass,\theta,R,\hat w)}$, $\mathrm{Tr}(\cdot\,\rho)$, the ratio $r$, $J$ and $Info$
-- statement:
--   Fix an attack and a seed. The probability of the outcome $(pass,\theta,R,\hat w)$ is
--
--   $$
--   p(pass,\theta,R,\hat w)=8^{-n}\sum_{w}\|M_{\hat w}|\psi_{w,\theta}\rangle\|^2,
--   $$
--
--   the sum running over the $w$ that give the test result $pass$. The effect $\Pi=M^\dagger M$ of that outcome acts on the classical register holding $(w,\theta')$ and the photons. Alice's preparation is $\rho=4^{-n}\sum_{w,\theta'}|w,\theta'\rangle\langle w,\theta'|_{\mathcal C}\otimes|\psi_{w,\theta'}\rangle\langle\psi_{w,\theta'}|$, and the ratio is
--
--   $$
--   r(pass,\theta,R,\hat w)=\frac{\mathrm{Tr}(P_0\,\Pi\,P_0\,\rho)}{\mathrm{Tr}(\Pi\,\rho)} .
--   $$
--
--   The module also defines the weight $8^{-n}\|M_{\hat w}|\psi_{\alpha,\hat\theta}\rangle\|^2$ of $(\theta,R,\hat w,\alpha)$ in the picture of p.13, where Alice prepares a random $|\psi_{\alpha,\hat\theta}\rangle$; the variable $J[E,\tau]=1$ iff $d_E(\alpha,\hat w)\le\tau$; and the event $Info=1$, the negation of $\|M_vP_0|\psi_{w,\theta}\rangle\|^2\le2^{-\gamma n}\|M_v|\psi_{w,\theta}\rangle\|^2$.
--
--   These are the quantities of the sketch in §10.
--
--   **Formalization Note** $\Pi$ is block diagonal on the classical register, so it is a family of operators on the photons indexed by $(w,\theta')$: the block is $2^{-n}M_{\hat w}^\dagger M_{\hat w}$ when $\theta'=\theta$ and $(w,\theta)$ gives $pass$, and $0$ otherwise. For such an operator $Q$, $\mathrm{Tr}(Q\rho)=4^{-n}\sum_{w,\theta'}\langle\psi_{w,\theta'}|Q_{w,\theta'}|\psi_{w,\theta'}\rangle$. The page's $J=0$ iff $d_E\le\tau n$ is inverted, since $Pass=J$ must be $1$ on the close side. In $Info$, $M_v$ is $K_y(t)M_{\hat w}$; the scalar and $P_{\mathcal C}$ of p.9 cancel at the run's own values.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §10, pp.13–14

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_Lsub
import Definitions.Def_MayersQKD_transcript

namespace MayersQKD

open MayersBC

variable {n r m : ℕ}

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.13: `p(pass, θ, R, ŵ)`, the probability of that outcome
for a fixed seed: `w`, `θ` uniform, `R` a uniform subset, `ŵ` with probability `‖M_ŵ|ψ_{w,θ}⟩‖²`,
and `pass` the test result. -/
noncomputable def outcomeProb (A : Attack n r m) (δ : ℝ) (s : A.Seed) (pass : Bool) (θ : Bases n)
    (R : Finset (Fin n)) (what : Bits n) : ℝ :=
  (1 / 8 : ℝ) ^ n * ∑ w ∈ Finset.univ.filter
    (fun w : Bits n => TestAccepted δ θ (A.commit s) w what R ↔ pass = true),
      ‖A.M s what (bb84State θ w)‖ ^ 2

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.13: `Π_(pass,θ,R,ŵ) = M† M`, with
`M = M_(θ,pass,R,ŵ)` the operation of that outcome on `|w, θ′⟩_C |ψ⟩`, as a family of blocks
indexed by the classical value `(w, θ′)`.

**Formalization Note.** The operation is `2^(−n/2) P_θ P_pass (I ⊗ M_ŵ)` (§6; `R` has probability
`2⁻ⁿ`, and (9)'s `8⁻ⁿ` confirms the square root). It is block diagonal on the classical register,
and the block of `Π` at `(w, θ′)` is `2⁻ⁿ M_ŵ† M_ŵ` if `θ′ = θ` and `(w, θ)` gives the test result
`pass`, and `0` otherwise. -/
noncomputable def testEffect (A : Attack n r m) (δ : ℝ) (s : A.Seed) (pass : Bool) (θ : Bases n)
    (R : Finset (Fin n)) (what : Bits n) (w : Bits n) (θ' : Bases n) : Photons n →ₗ[ℂ] Photons n :=
  if θ' = θ ∧ (TestAccepted δ θ' (A.commit s) w what R ↔ pass = true) then
    ((1 / 2 : ℂ) ^ n) • (LinearMap.adjoint (A.M s what) ∘ₗ A.M s what)
  else 0

/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.13: `Tr(Q ρ)` for Alice's preparation
`ρ = 4⁻ⁿ ∑_{w,θ} |w, θ⟩⟨w, θ|_C ⊗ |ψ_{w,θ}⟩⟨ψ_{w,θ}|` and a block-diagonal operator `Q` with blocks
`Q w θ`: this is `4⁻ⁿ ∑_{w,θ} ⟨ψ_{w,θ}|Q w θ|ψ_{w,θ}⟩`. -/
noncomputable def prepTrace (Q : Bits n → Bases n → Photons n →ₗ[ℂ] Photons n) : ℂ :=
  (1 / 4 : ℂ) ^ n * ∑ w, ∑ θ', inner ℂ (bb84State θ' w) (Q w θ' (bb84State θ' w))

/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.13: the ratio
`r(pass, θ, R, ŵ) = Tr(P₀ Π P₀ ρ) / Tr(Π ρ)`, for a fixed seed and a fixed `c`.

**Formalization Note.** `P₀` acts on the photons only, so its block is the same at every `(w, θ′)`.
Both traces are real; `.re` only changes the type. The value at a null outcome is `0`. -/
noncomputable def ratioR (A : Attack n r m) (δ ε : ℝ) (s : A.Seed) (c pass : Bool) (θ : Bases n)
    (R : Finset (Fin n)) (what : Bits n) : ℝ :=
  (prepTrace (fun w θ' => P0 A ε s what R θ c ∘ₗ testEffect A δ s pass θ R what w θ' ∘ₗ
      P0 A ε s what R θ c) /
    prepTrace (testEffect A δ s pass θ R what)).re

/-- Mayers, arXiv:quant-ph/9606003v1, §10, pp.13–14: the weight of `(θ, R, ŵ, α)` in the picture of
p.13: Alice chooses `θ` and `R` as usual but prepares a perfectly random `|ψ_{α,θ̂}⟩`; Bob's outcome
`ŵ` then has probability `‖M_ŵ|ψ_{α,θ̂}⟩‖²`. The total factor is `8⁻ⁿ`. -/
noncomputable def alphaWeight (A : Attack n r m) (s : A.Seed)
    (x : Bases n × Finset (Fin n) × Bits n × Bits n) : ℝ :=
  (1 / 8 : ℝ) ^ n * ‖A.M s x.2.2.1 (bb84State (A.commit s) x.2.2.2)‖ ^ 2

/-- Mayers, arXiv:quant-ph/9606003v1, §10, pp.13–14: `J[E, τ] = 1`, i.e. `d_E(α, ŵ) ≤ τ`.

**Formalization Note.** The page prints `J = 0` iff `d_E(α, ŵ) ≤ τn`, which is inverted: `Pass`
and `P_pass` need `J = 1` on the close side (`P₁` is the close subspace), and the events of p.14
are right once `J` is fixed. -/
def J (E : Finset (Fin n)) (τ : ℝ) (α what : Bits n) : Prop := (posDist E α what : ℝ) ≤ τ

/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.13: `Info = 1`, i.e. the negation of
`‖M_v P₀|ψ_{w,θ}⟩‖² ≤ 2^(−γn) ‖M_v|ψ_{w,θ}⟩‖²`, at a run with a fixed seed and a fixed `c`.

**Formalization Note.** Here `M_v` is `K_y(t) M_ŵ`. The factor `2^(−(n+1)) P_C` of p.9 acts as the
same scalar on both sides at the run's own `(b, w, θ)`, so it cancels. -/
def InfoOne (A : Attack n r m) (δ ε γ : ℝ) (s : A.Seed) (c : Bool) (x : Run A) : Prop :=
  match x with
  | (b, w, θ, R, f, what, y) =>
    let Mv := A.K (transcript A δ b w θ R f c s what) y ∘ₗ A.M s what
    ¬ ‖Mv (P0 A ε s what R θ c (bb84State θ w))‖ ^ 2 ≤
        (2 : ℝ) ^ (-γ * n) * ‖Mv (bb84State θ w)‖ ^ 2

end MayersQKD


