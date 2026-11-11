-- Prove2me | Definitions.Def_RandPurIso_Completion_OracleAlg
-- name    : RandPurIso_Completion_OracleAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:15.073458+00:00
-- url     : https://prove2.me/theorems/506d59c1-2fd6-415a-84de-94cf9428ce0c
-- title:
--   Oracle algorithm and its output $A^O$ (Definition 3.2)
-- statement:
--   An **oracle algorithm** with workspace $\mathsf W$ is a list of CPTP maps $A_1,\dots,A_t:\mathbf L(\mathsf{Out}\otimes\mathsf W)\to\mathbf L(\mathsf{In}\otimes\mathsf W)$, a final CPTP map $A_{t+1}$ on $\mathbf L(\mathsf{Out}\otimes\mathsf W)$ and an initial density matrix $\rho$ on $\mathsf{Out}\otimes\mathsf W$; it makes $t$ queries. Its output with oracle $O$ is
--   $$A^O=\operatorname{Tr}_{\mathsf{St}}\big((A_{t+1}\cdot O\cdot A_t\cdots O\cdot A_1)(\rho\otimes|\varphi_0\rangle\langle\varphi_0|_{\mathsf{St}})\big),$$
--   where each $A_i$ acts with the identity on $\mathsf{St}$ and the oracle with the identity on $\mathsf W$.
--
--   **Formalization Note** The paper fixes $\rho=|0\rangle\langle 0|$ "without loss of generality" ($A_1$ can prepare any state); here $\rho$ is part of the algorithm and may be any density matrix, which contains that case. The number of queries is the length of the list of steps.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.2, p. 17

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_RandPurIso_Completion_IsCPTP
import Definitions.Def_RandPurIso_Completion_Oracle
open Matrix

namespace RandPurIso.Completion

/-- **Oracle algorithm** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.2, p. 17).

An oracle algorithm with query input register `In`, query output register `Out` and workspace `W`
is a list of CPTP maps `A₁, …, A_t : L(Out ⊗ W) → L(In ⊗ W)` (`steps`), a final CPTP map
`A_{t+1} : L(Out ⊗ W) → L(Out ⊗ W)` (`final`) and an initial density matrix `ρ` on `Out ⊗ W`
(`init`). It makes `t = steps.length` queries (`numQueries`).

**Formalization Note.** Definition 3.2 runs the algorithm on an arbitrary initial state
`ρ_{Out,A}` and then fixes `ρ = |0⟩⟨0|` "without loss of generality". Here the initial state is
part of the algorithm and may be any density matrix; this contains the `|0⟩⟨0|` case. -/
structure OracleAlg (In Out W : Type) [Fintype In] [Fintype Out] [Fintype W] where
  /-- the initial state `ρ_{Out,A}` -/
  init : Matrix (Out × W) (Out × W) ℂ
  /-- `A₁, …, A_t`, in the order they are applied -/
  steps : List (Matrix (Out × W) (Out × W) ℂ → Matrix (In × W) (In × W) ℂ)
  /-- `A_{t+1}` -/
  final : Matrix (Out × W) (Out × W) ℂ → Matrix (Out × W) (Out × W) ℂ
  init_density : PeresTerno.IsDensityMatrix init
  steps_cptp : ∀ f ∈ steps, IsCPTP f
  final_cptp : IsCPTP final

/-- The number of oracle queries `t` of an oracle algorithm (Definition 3.2). -/
def OracleAlg.numQueries {In Out W : Type} [Fintype In] [Fintype Out] [Fintype W]
    (A : OracleAlg In Out W) : ℕ := A.steps.length

/-- An oracle acting on `(In ⊗ W) ⊗ St` with the identity on the algorithm's workspace `W`:
`(O ⊗ id_W)`, written blockwise. -/
def Oracle.onWork {In Out St W : Type} (O : Oracle In Out St)
    (R : Matrix ((In × W) × St) ((In × W) × St) ℂ) : Matrix ((Out × W) × St) ((Out × W) × St) ℂ :=
  fun p q => O.map (fun a b => R ((a.1, p.1.2), a.2) ((b.1, q.1.2), b.2)) (p.1.1, p.2) (q.1.1, q.2)

/-- **The output `A^O` of an oracle algorithm** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.2, p. 17):
`A^O = Tr_St((A_{t+1} · O · A_t ⋯ O · A_1)(ρ_{Out,A} ⊗ |φ₀⟩⟨φ₀|_St))`, where each `A_i` acts with
the identity on `St` and the oracle acts with the identity on the workspace. -/
noncomputable def OracleAlg.run {In Out W St : Type} [Fintype In] [Fintype Out] [Fintype W]
    [Fintype St] (A : OracleAlg In Out W) (O : Oracle In Out St) : Matrix (Out × W) (Out × W) ℂ :=
  let ρ0 : Matrix ((Out × W) × St) ((Out × W) × St) ℂ :=
    fun p q => A.init p.1 q.1 * (O.init p.2 * star (O.init q.2))
  let ρT := A.steps.foldl (fun ρ f => O.onWork (PeresTerno.ampliate f ρ)) ρ0
  let ρF := PeresTerno.ampliate A.final ρT
  fun p q => ∑ s : St, ρF (p, s) (q, s)

end RandPurIso.Completion


