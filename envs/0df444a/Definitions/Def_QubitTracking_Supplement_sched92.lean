-- Prove2me | Definitions.Def_QubitTracking_Supplement_sched92
-- name    : QubitTracking_Supplement_sched92
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:12:37.979218+00:00
-- url     : https://prove2.me/theorems/63bf7eaa-a2c5-4775-b3cc-505e088c2bb4
-- title:
--   Schedules of Constructions 8.3 and 9.2 at a claimed point $(L,t)$, their parameters, and a prover at position $L$
-- statement:
--   Two verifiers sit at positions $-1$ ($\mathcal V_L$) and $1$ ($\mathcal V_R$). For a claimed point $(L,t)$ with $L\in[-1,1]$ and a localization parameter $\Delta$, the protocols of §8 and §9.1 send their challenges so that both challenges of round $i$ reach $L$ exactly at a checkpoint $t_i$:
--
--   1. **Construction 8.3** (two rounds): $\delta=\Delta/2$, checkpoints $t_i=t+i\delta$ for $i=0,1$;
--   2. **Construction 9.2** (also used by Construction 9.8): for a repetition factor $\gamma$, $\delta=\Delta/(\gamma+2)$, checkpoints $t_i=t+i\delta$ for $i=0,1,\dots,\gamma$.
--
--   In round $i$, $\mathcal V_L$ broadcasts at $t_i-(L+1)$ and expects its response at $t_i+(L+1)$; $\mathcal V_R$ broadcasts at $t_i-(1-L)$ and expects its response at $t_i+(1-L)$.
--
--   The module also fixes the parameter conditions. For Construction 8.3: $n,m$ polynomially bounded with $n(\lambda),m(\lambda)\ge\lambda$ and $\Delta(\lambda)>0$, with no upper bound on $\Delta$. For Constructions 9.2 and 9.8: in addition $\Delta(\lambda)\le 1$, and a repetition factor $\gamma(\lambda)\ge1$ that is polynomially bounded. Finally, a prover is **at position $L$** if every gate it applies is located at $L$ and its input cells (the register $\mathbf B$) stay at $L$ at all times.
--
--   These schedules plug into the published protocol of Construction 9.5 (the oracles, the anchor state, the acceptance test and the extraction event are generic in the schedule), which is how Theorems 8.4, 9.3 and 9.9 are stated.
--
--   **Formalization Note** Time is a real number. Construction 9.2 says "for $i=0,1$" in $\mathcal V_R$'s line; every checkpoint $i\le\gamma$ is sent, as in $\mathcal V_L$'s line and in the proof of Theorem 9.3. Unlike Construction 9.5, $1/\Delta$ need not be polynomially bounded, since the number of rounds does not depend on $\Delta$.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Construction 8.3, p.57; Construction 9.2, pp.62–63; Construction 9.8, pp.69–70; Definitions 8.1, 9.1, 9.7 (α-Completeness), pp.56, 62, 68

import Definitions.Def_QubitTracking_sched95

set_option autoImplicit false

open Matrix

namespace QubitTracking.Supplement

/-! The schedules of Construction 8.3 (two rounds) and Construction 9.2 (`γ + 1` checkpoints) at a
fixed claimed point `(L, t)`, their parameter conditions, and "a prover at position `L`".

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Construction 8.3,
p.57, Construction 9.2, pp.62–63, Construction 9.8, pp.69–70. -/

/-- **The schedule of Construction 8.3** (p.57) at the claimed point `(L, t)` with localization
parameter `Δ`: `δ = Δ/2` and rounds `i = 0, 1`; `𝒱_L` broadcasts at `t + iδ − (L + 1)` and expects
its response at `t + iδ + (L + 1)`; `𝒱_R` broadcasts at `t + iδ − (1 − L)` and expects its response
at `t + iδ + (1 − L)`. Both challenges of round `i` reach `L` at time `t + iδ`. -/
noncomputable def sched83 (L t Δ : ℝ) : Sched where
  N := 1
  sendL i := t + (i : ℝ) * (Δ / 2) - (L + 1)
  sendR i := t + (i : ℝ) * (Δ / 2) - (1 - L)
  deadL i := t + (i : ℝ) * (Δ / 2) + (L + 1)
  deadR i := t + (i : ℝ) * (Δ / 2) + (1 - L)

/-- **The schedule of Construction 9.2** (p.63), also used by Construction 9.8 (p.70), at the
claimed point `(L, t)` with localization parameter `Δ` and repetition factor `γ`:
`δ = Δ/(γ + 2)`, checkpoints `t_i = t + iδ` for `i = 0, 1, …, γ`; `𝒱_L` broadcasts at
`t_i − (L + 1)` and expects its response at `t_i + (L + 1)`; `𝒱_R` broadcasts at `t_i − (1 − L)`
and expects its response at `t_i + (1 − L)`.

**Formalization Note** The construction's text says "for `i = 0, 1`" in `𝒱_R`'s line; every
checkpoint `i ≤ γ` is sent, as in `𝒱_L`'s line and in the proof of Theorem 9.3 (p.63). -/
noncomputable def sched92 (L t Δ : ℝ) (γ : ℕ) : Sched where
  N := γ
  sendL i := t + (i : ℝ) * (Δ / ((γ : ℝ) + 2)) - (L + 1)
  sendR i := t + (i : ℝ) * (Δ / ((γ : ℝ) + 2)) - (1 - L)
  deadL i := t + (i : ℝ) * (Δ / ((γ : ℝ) + 2)) + (L + 1)
  deadR i := t + (i : ℝ) * (Δ / ((γ : ℝ) + 2)) + (1 - L)

/-- **The parameters of Construction 8.3** (p.57: "`n(λ), m(λ) ≥ λ` be polynomials. Take some
localization parameter `Δ(λ)`"): `n, m` polynomially bounded with `n(λ), m(λ) ≥ λ`, and
`Δ(λ) > 0`. No upper bound on `Δ` is imposed. -/
def Params84 (n m : ℕ → ℕ) (Δ : ℕ → ℝ) : Prop :=
  PPADSIS.SubexpSIS.PolyBounded n ∧ PPADSIS.SubexpSIS.PolyBounded m ∧
    (∀ l, l ≤ n l ∧ l ≤ m l) ∧ (∀ l, 0 < Δ l)

/-- **The parameters of Constructions 9.2 and 9.8** (p.62, p.69: "`n(λ), m(λ) ≥ λ` be
polynomials. Take a localization parameter `Δ(λ) ≤ 1` and a repetition factor `γ(λ)`"): `n, m`
polynomially bounded with `n(λ), m(λ) ≥ λ`; `0 < Δ(λ) ≤ 1`; `γ(λ) ≥ 1` and `γ` polynomially
bounded (the verifier, which sends `γ + 1` rounds, is PPT, p.61).

**Formalization Note** Unlike Construction 9.5, `1/Δ` need not be polynomially bounded: the
number of rounds does not depend on `Δ`. -/
def Params92 (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ) : Prop :=
  PPADSIS.SubexpSIS.PolyBounded n ∧ PPADSIS.SubexpSIS.PolyBounded m ∧
    (∀ l, l ≤ n l ∧ l ≤ m l) ∧ (∀ l, 0 < Δ l ∧ Δ l ≤ 1) ∧ (∀ l, 1 ≤ γ l) ∧
    PPADSIS.SubexpSIS.PolyBounded γ

/-- **A prover at position `L`** (α-Completeness of Definitions 8.1, 9.1, 9.7: "a QPT prover `𝒫`
at position `(L, t)`"; the honest prover "consists of a single party always holding the `𝐁`
register at location `L`", pp.58, 63, 70): every gate is located at `L` and the input cells (the
register `𝐁`) stay at `L` at all times. -/
def IsAtPoint {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}
    (P : Prover σ lam inLen respLen κ inL outL) (L : ℝ) : Prop :=
  (∀ g ∈ P.gates, g.pos = L) ∧ ∀ j s, P.traj (P.input j) s = L

end QubitTracking.Supplement


