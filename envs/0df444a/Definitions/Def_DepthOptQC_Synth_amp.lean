-- Prove2me | Definitions.Def_DepthOptQC_Synth_amp
-- name    : DepthOptQC_Synth_amp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:57.769479+00:00
-- url     : https://prove2.me/theorems/e768465c-447a-495d-a460-97c283706880
-- title:
--   The isometry $V_0$, projector $\Pi$, reflection $R_\Pi$, block $\mathcal B(W)$ and one OAA step $\mathrm{Amp}(W)$
-- statement:
--   Let $A$ be an ancilla register with all-zero basis state $|0\rangle_A$ and $S$ a system register. Define
--   $$
--   V_0 := |0\rangle_A\otimes I_S,\qquad \Pi := V_0V_0^\dagger,\qquad R_\Pi := I-2\Pi ,
--   $$
--   so $V_0$ embeds the system into the all-zero ancilla subspace, $\Pi$ projects onto that subspace and $R_\Pi$ applies a phase $-1$ exactly on it. For an operator $W$ on $A\otimes S$, its **distinguished block** is $\mathcal B(W):=V_0^\dagger W V_0$, and **one step of oblivious amplitude amplification** is
--   $$
--   \mathrm{Amp}(W) := W\,R_\Pi\,W^\dagger\,R_\Pi\,W .
--   $$
--   If $\mathcal B(W)=U/2$ for a unitary $U$, then $\mathrm{Amp}(W)V_0=-V_0U$: one step turns a block encoding of $\tfrac12U$ into an exact implementation of $U$ up to the sign $-1$.
--
--   **Formalization Note** The ancilla register is any finite type with a distinguished point (the paper's $a$-qubit register with $0^a$), the system any finite type; the ancilla factor comes first, as in the paper.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §3.3.1, Eqs. (58)–(60), pp.20–21

import Mathlib

namespace DepthOptQC.Synth

variable {A Sy : Type*} [Fintype A] [DecidableEq A] [Fintype Sy] [DecidableEq Sy]

/-- **The isometry `V₀ := |0^a⟩_A ⊗ I_S`** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (58), p.20), embedding the system register `Sy` into the all-zero ancilla
subspace: its `((a, s'), s)` entry is `1` iff `a = a₀` and `s' = s`.

**Formalization Note.** The ancilla register is any finite type `A` with a distinguished basis point
`a₀` (the paper's `A` is an `a`-qubit register with `a₀ = 0^a`); the ancilla factor comes first, as
in the paper. -/
def V0 (a₀ : A) : Matrix (A × Sy) Sy ℂ :=
  Matrix.of fun p s => if p.1 = a₀ ∧ p.2 = s then 1 else 0

/-- **The projector `Π := V₀V₀†`** onto the all-zero ancilla subspace (Vasconcelos,
arXiv:2609.34659, Eq. (58), p.20). -/
def proj (a₀ : A) : Matrix (A × Sy) (A × Sy) ℂ :=
  V0 (Sy := Sy) a₀ * (V0 (Sy := Sy) a₀).conjTranspose

/-- **The reflection `R_Π := I − 2Π`** (Vasconcelos, arXiv:2609.34659, Eq. (58), p.20): phase `−1`
exactly on the all-zero ancilla subspace. -/
def reflR (a₀ : A) : Matrix (A × Sy) (A × Sy) ℂ :=
  1 - (2 : ℂ) • proj (Sy := Sy) a₀

/-- **The distinguished block `B(W) := V₀† W V₀`** (Vasconcelos, arXiv:2609.34659, §3.3.1, p.21). -/
def block (a₀ : A) (W : Matrix (A × Sy) (A × Sy) ℂ) : Matrix Sy Sy ℂ :=
  (V0 (Sy := Sy) a₀).conjTranspose * W * V0 (Sy := Sy) a₀

/-- **One step of oblivious amplitude amplification** (Vasconcelos, arXiv:2609.34659, Eq. (60),
p.21): `Amp(W) := W R_Π W† R_Π W`. -/
def amp (a₀ : A) (W : Matrix (A × Sy) (A × Sy) ℂ) : Matrix (A × Sy) (A × Sy) ℂ :=
  W * reflR (Sy := Sy) a₀ * W.conjTranspose * reflR (Sy := Sy) a₀ * W

end DepthOptQC.Synth


