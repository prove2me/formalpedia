-- Prove2me | Definitions.Def_FourMsgQMA_WQ
-- name    : FourMsgQMA_WQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:53.66026+00:00
-- url     : https://prove2.me/theorems/98ad383c-49a5-4119-ac36-9a7176b6af22
-- title:
--   QMA verification families and witness sets $W_Q(x,a)$
-- statement:
--   Let $L=(L_{\mathrm{yes}},L_{\mathrm{no}})$ be a promise problem and $F$ a family of quantum verification circuits: on an input $x$ of length $n$, the layered circuit $Q_x$ over $\{H,S,T,X,\mathrm{CNOT}\}$ acts on $n$ input wires, $w(n)$ witness wires and $a(n)+1$ ancilla wires, and its output wire is measured.
--
--   $F$ is a **QMA verifier for $L$** when it is polynomial-time uniform, well formed and polynomially bounded, every $x\in L_{\mathrm{yes}}$ has a unit witness vector accepted with probability at least $2/3$, and on $x\in L_{\mathrm{no}}$ every unit witness vector is accepted with probability at most $1/3$. This is the body of the published `PromiseQMA` for the family $F$.
--
--   For a density operator $\rho$ on the witness register, $\Pr[Q_x(\rho)=1]=\operatorname{Re}\operatorname{tr}(E_x\rho)$, with the acceptance effect $E_x$ whose entries are
--   $$
--   (E_x)_{ab}=\sum_{y:\,y_{\mathrm{out}}=1}\overline{\Phi_a(y)}\,\Phi_b(y),
--   $$
--   where $\Phi_b$ is the circuit's output on $|x\rangle|b\rangle|0\cdots0\rangle$. The witness set at threshold $a$ is
--   $$
--   W_Q(x,a)=\{\rho\ \text{density operator} : \Pr[Q_x(\rho)=1]\ge a\}.
--   $$
--   The **local cost** of an instance is $t_L(x)=|x|+w(|x|)+a(|x|)+1+\operatorname{depth}(Q_x)$.
--
--   $W_Q(x,2/3)$ is the honest witness set of every completeness statement in the mission; $t_L$ replaces the paper's local resource bound $T$.
--
--   **Formalization Note** Pinned-down version (operator request). Witnesses may be mixed; for a pure witness the effect gives the published `QMAFamily.acceptWith` (proved in the mission's sanity file). $T$ is replaced by $t_L$: the paper's $T$ "bounds the resources of one amplified base verification" and is "polynomial in λ and in the cost of verifying one original QMA instance" (p.9).
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.2, pp.9–10 (PDF 11–12); §3.1, p.9 (resource parameters)

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.2, pp.9–10 (PDF 11–12): QMA promise
problems, their verification circuits `Q_x` and the witness sets `W_Q(x, a)`.
-/

open QAlgorithms QAlgorithms.Complexity
open scoped ComplexOrder

/-- A density operator on `n` qubits: positive semidefinite with trace one (§3.1, p.8: `D(H)`). -/
def IsDensity {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- `F` is a uniform QMA verification-circuit family for the promise problem `L` (§3.2, p.9:
"Let `L = (L_yes, L_no)` be a QMA promise problem with a uniform verification circuit `Q_x`"):
`F` is polynomial-time uniform, well formed and polynomially bounded, every `x ∈ L_yes` has a
normalized witness accepted with probability at least `2/3`, and on `x ∈ L_no` every normalized
witness is accepted with probability at most `1/3` (p.10). This is the body of the published
`QAlgorithms.Complexity.PromiseQMA` for the family `F`. -/
def IsQMAVerifierFor (L : PromiseProblem) (F : QMAFamily) : Prop :=
  Uniform F.toFamily ∧ WellFormed F.toFamily ∧ PolyBounded F.toFamily ∧
    ∀ w : Str,
      (w ∈ L.yes → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
          (2 : ℝ) / 3 ≤ F.acceptWith (toBits w) ψ) ∧
      (w ∈ L.no → ∀ ψ : QState (F.wit w.length), Normalized ψ →
          F.acceptWith (toBits w) ψ ≤ (1 : ℝ) / 3)

/-- The image of the computational-basis witness `|b⟩` under the verification circuit of `F` on
input `x`: the circuit is run on `|x⟩|b⟩|0…0⟩`. -/
noncomputable def qmaColumn (F : QMAFamily) (x : Str) (b : Qubits (F.wit x.length)) :
    QState (x.length + (F.wit x.length + (F.anc x.length + 1))) :=
  runLayered (F.circ x.length) (witnessInputState F (toBits x) (fun c => if c = b then 1 else 0))

/-- The acceptance effect of `Q_x` on the witness register: `E_{ab} = ∑_y [y_out = 1]
\overline{Φ_a(y)} Φ_b(y)`, with `Φ_b` the circuit's output on the basis witness `|b⟩`. For a
witness vector `ψ`, `⟨ψ|E|ψ⟩` is the published `QMAFamily.acceptWith`, and for a density operator
`ρ`, `Pr[Q_x(ρ) = 1] = Re tr(E ρ)`. -/
noncomputable def qmaEffect (F : QMAFamily) (x : Str) :
    Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ :=
  Matrix.of fun a b =>
    ∑ y : Qubits (x.length + (F.wit x.length + (F.anc x.length + 1))),
      if y (F.out x.length) then star (qmaColumn F x a y) * qmaColumn F x b y else 0

/-- `Pr[Q_x(ρ) = 1]` for a (possibly mixed) witness `ρ` on the witness register. -/
noncomputable def qmaAccept (F : QMAFamily) (x : Str)
    (ρ : Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) : ℝ :=
  (Matrix.trace (qmaEffect F x * ρ)).re

/-- §3.2, p.9: `W_Q(x, a) = {ρ : Pr[Q_x(ρ) = 1] ≥ a}`, the witness density operators accepted by
the verification circuit on input `x` with probability at least `a`.

**Formalization Note** Witnesses are density operators (they may be mixed); the acceptance
probability of a mixed witness is `Re tr(E ρ)` with `E = qmaEffect F x`. -/
def WQ (F : QMAFamily) (x : Str) (a : ℝ) :
    Set (Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) :=
  {ρ | IsDensity ρ ∧ a ≤ qmaAccept F x ρ}

/-- The local cost `t_L(x)` of verifying one instance `x` with `F`: input length, witness and
ancilla wires (with the output wire), and circuit depth. The pinned-down version uses
`t(X) = max_i t_L(x_i)` in place of the paper's resource bound `T`, which "bounds the resources of
one amplified base verification, including witness copies" and is "polynomial in λ and in the cost
of verifying one original QMA instance" (§3.1, p.9). -/
def localCost (F : QMAFamily) (x : Str) : ℕ :=
  x.length + F.wit x.length + F.anc x.length + 1 + depth (F.circ x.length)

end FourMsgQMA


