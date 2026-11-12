-- Prove2me | Definitions.Def_QPVEntanglement_Draw
-- name    : QPVEntanglement_Draw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:30:20.908198+00:00
-- url     : https://prove2.me/theorems/aac723b7-af92-48be-b25e-4f1f491df1a6
-- title:
--   The verifiers' random draw and the ordered label list
-- statement:
--   The verifiers' randomness is drawn uniformly from the finite set of tuples $\xi=(x,\theta,b,i,u)$: the BB84 bit $x_h$ and basis $\theta_h$ of every label $h<N_L$, and for every round $k$ the selected verifier $b_k\in\{0,1\}$, the challenge slot $i_k\in\{0,\dots,s-1\}$ and the list index $u_k\in\{0,\dots,R_H-1\}$. The ordered label list is $S_0=[0,\dots,R_H-1]$; the requested label of round $k$ is $r_k=S_k[u_k]$, and $S_{k+1}$ is $S_k$ with that entry removed (order kept) followed by the replenishment label $R_H+k$. The state of label $h$ is $|\psi_h\rangle=H^{\theta_h}|x_h\rangle$, $H$ the Hadamard matrix.
--
--   **Formalization Note** Sampling the list index uniformly is the same as sampling $r_k$ uniformly among the $R_H$ stored labels (Figure 3).
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Figure 3, p.31

import Mathlib
import Definitions.Def_QPVEntanglement_Schedule

set_option autoImplicit false

namespace QPVEntanglement

/-- **The verifiers' random draw** (Figure 3, p.31). Behera–Goyal, arXiv:2609.39234 (sha256
bdf2928d…), Figure 3, p.31.

`Draw m RH s` is the finite set of all values of the verifiers' private randomness:
`(xs, θs, b, i, u)` where `xs h, θs h ∈ {0,1}` are the BB84 bit and basis of label `h`, and, for
each round `k`, `b k ∈ {0,1}` is the selected verifier, `i k ∈ [s]` the challenge slot and
`u k ∈ [R_H]` the position (list index) of the requested label in the ordered list `S`. It is
drawn uniformly.

**Formalization Note.** Pinned model P4. Sampling the list index `u k` uniformly is the same as
sampling the requested label `r_k` uniformly among the `R_H` labels currently stored ("samples a
label `r_k` uniformly from the `R_H` distinct labels currently stored in `S`", p.31). All
indices are 0-based. -/
abbrev Draw (m RH s : ℕ) : Type :=
  (Fin (NL m RH) → Fin 2) × (Fin (NL m RH) → Fin 2) × (Fin m → Fin 2) × (Fin m → Fin s) ×
    (Fin m → Fin RH)

namespace Draw

variable {m RH s : ℕ}

/-- BB84 bit `x_h` of label `h`. -/
def xs (ξ : Draw m RH s) : Fin (NL m RH) → Fin 2 := ξ.1
/-- BB84 basis `θ_h` of label `h`. -/
def θs (ξ : Draw m RH s) : Fin (NL m RH) → Fin 2 := ξ.2.1
/-- Selected verifier `b_k` of round `k`. -/
def b (ξ : Draw m RH s) : Fin m → Fin 2 := ξ.2.2.1
/-- Challenge slot `i_k` of round `k`. -/
def i (ξ : Draw m RH s) : Fin m → Fin s := ξ.2.2.2.1
/-- Requested list index `u_k` of round `k`. -/
def u (ξ : Draw m RH s) : Fin m → Fin RH := ξ.2.2.2.2

/-- The ordered label list `S_k` immediately before round `k` (Figure 3): `S₀ = [0, …, R_H−1]`,
and `S_{k+1}` is `S_k` with its `u_k`-th entry removed (order kept), followed by the
replenishment label `R_H + k` when `k + 1 < m` ("Remove the record labeled `r_k` from `S`
without changing the order of the remaining records", "appends the labeled record to `S`",
p.31). -/
def labelList (ξ : Draw m RH s) : ℕ → List (Fin (NL m RH))
  | 0 => List.ofFn fun h : Fin RH => (⟨h.val, by have := h.isLt; simp only [NL]; omega⟩ : Fin (NL m RH))
  | k + 1 =>
      if hk : k < m then
        (ξ.labelList k).eraseIdx (ξ.u ⟨k, hk⟩).val ++
          (if h : RH + k < NL m RH then [(⟨RH + k, h⟩ : Fin (NL m RH))] else [])
      else ξ.labelList k

/-- The requested label `r_k = S_k[u_k]` of round `k` (always `some`, since `S_k` has `R_H`
entries). -/
def req (ξ : Draw m RH s) (k : Fin m) : Option (Fin (NL m RH)) :=
  (ξ.labelList k.val)[(ξ.u k).val]?

end Draw

/-- The Hadamard matrix `H = (1/√2)[[1,1],[1,−1]]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r c => (1 / Real.sqrt 2 : ℂ) * (if r = 1 ∧ c = 1 then -1 else 1)

/-- The BB84 state `H^θ |x⟩` (Figure 3: "prepare `|ψ⟩_{r_j} = H^{θ_{r_j}} |x_{r_j}⟩`"), as a
vector of `ℂ²`; `H⁰ = I`. -/
noncomputable def bb84 (x θ : Fin 2) : Fin 2 → ℂ :=
  (if θ = 1 then hadamard else 1).mulVec (Pi.single x 1)

/-- The state `|ψ_h⟩ = H^{θ_h}|x_h⟩` of label `h` under the draw `ξ`. -/
noncomputable def Draw.psi {m RH s : ℕ} (ξ : Draw m RH s) (h : Fin (NL m RH)) : Fin 2 → ℂ :=
  bb84 (ξ.xs h) (ξ.θs h)

end QPVEntanglement


