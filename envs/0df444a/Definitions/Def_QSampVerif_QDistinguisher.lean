-- Prove2me | Definitions.Def_QSampVerif_QDistinguisher
-- name    : QSampVerif_QDistinguisher
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:37.599203+00:00
-- url     : https://prove2.me/theorems/7d2ea0ed-00f5-4bb3-b103-2dae8b0a6ffb
-- title:
--   Quantum distinguishers with classical advice and the distinguishing advantage
-- statement:
--   A **quantum distinguisher** $D$ has $n$ wires started in $|0\cdots0\rangle$. Its classical input $z\in\{\bot\}\cup\{0,1\}^*$ is encoded ($\bot\mapsto0$, $s\mapsto1s$), written as $\mathrm{padEnc}$ into designated input wires by $X$ flips, a layered Clifford+T circuit runs, and one output wire is measured; $\Pr[D(z)=1]$ is the Born probability of outcome $1$. Its size is the number of wires, input wires and instructions, plus one. Any advice is hard-wired, so $D$ may depend on $\lambda$ and $C$.
--
--   The **distinguishing advantage** between two distributions $\mu,\nu$ on verifier outputs is, as in (484),
--
--   $$\mathrm{adv}_D(\mu,\nu)=\Bigl|\Pr_{z\sim\mu}[D(z)=1]-\Pr_{z\sim\nu}[D(z)=1]\Bigr| .$$
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.2, (484), p.185 (PDF 186); §3.11, p.23 (PDF 24); paper.md decision 8

import Definitions.Def_QSampVerif_tup

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Theorem 14.2, p.185 (PDF 186): "every efficient quantum distinguisher D"; §3.11, p.23:
"polynomial-size quantum circuits with nonuniform classical advice".

A quantum distinguisher: `n` wires started in `|0…0⟩`; the classical input `z` is written into
the wires `inW` by `X` flips (as `padEnc (encOpt z)`, so `⊥` and every string are told apart);
a layered Clifford+T circuit runs; the wire `outWire` is measured and `1` means "real". -/
structure QDistinguisher where
  /-- Number of wires. -/
  n : ℕ
  /-- Wires receiving the classical input. -/
  inW : List (Fin n)
  /-- The circuit. -/
  circ : Layered n
  /-- The measured output wire. -/
  outWire : Fin n

namespace QDistinguisher

/-- The size of a distinguisher: wires, input wires, instructions and the output wire. -/
def size (D : QDistinguisher) : ℕ := D.n + D.inW.length + numInstr D.circ + 1

/-- A distinguisher is well formed: distinct input wires, disjoint gates in each layer. -/
def Valid (D : QDistinguisher) : Prop := D.inW.Nodup ∧ ∀ l ∈ D.circ, LayerOk l

/-- `Pr[D(z) = 1]`: the Born probability that the output wire reads `1`. -/
noncomputable def accept (D : QDistinguisher) (z : Option Str) : ℝ :=
  ∑ y : Qubits D.n,
    if y D.outWire then
      ‖runLayered D.circ (loadX D.inW (padEnc (encOpt z)) (zeroState D.n)) y‖ ^ 2 else 0

end QDistinguisher

/-- The distinguishing advantage (484), p.185:
`|Pr_{z∼μ}[D(z) = 1] − Pr_{z∼ν}[D(z) = 1]|`. -/
noncomputable def advantage (D : QDistinguisher) (μ ν : Option Str → ℝ) : ℝ :=
  |∑' z : Option Str, μ z * D.accept z - ∑' z : Option Str, ν z * D.accept z|

end QSampVerif


