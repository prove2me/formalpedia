-- Prove2me | Definitions.Def_QuantumPRC_Supplement_C816
-- name    : QuantumPRC_Supplement_C816
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:36:00.59122+00:00
-- url     : https://prove2.me/theorems/e9609c20-06cd-4c08-945b-1708a5c78859
-- title:
--   Construction 8.16: keyed CWS code from a classical code
-- statement:
--   Fix a classical encoder $C:\{0,1\}^{n_L}\to\{0,1\}^{n_P}$ with decoder $D$, where $n_P=2n$ is even, a radius function $t$, and a pair of algorithms (GraphSample, Recover) as in Theorem 7.1. **Construction 8.16** is the following keyed code from $n_L$ to $n_P$ qubits.
--
--   1. **KeyGen**: sample a graph $G\leftarrow\mathrm{GraphSample}(1^{n_P/2})$ (at radius $t(n_P)$) and an independent uniformly random Pauli operator $P\in\mathcal P_{n_P}$; output $\mathsf{sk}=(G,P)$.
--   2. **Enc**: $\mathrm{Enc}_{\mathsf{sk}}=P\,U_G\,V_C$, where $V_C|x\rangle=|C(x)\rangle$ (250) and $U_G=\big(\prod_{\{i,j\}\in E(G)}CZ_{ij}\big)H^{\otimes n_P}$ is the CWS encoding unitary of Definition 3.14.
--   3. **Dec**: apply $U_G^\dagger P^\dagger$; append $n_L$ qubits in $|0\rangle$ and apply $|y\rangle_{\mathbf B}|0\rangle_{\mathbf A}\mapsto|y\oplus C(D(y))\rangle_{\mathbf B}|D(y)\rangle_{\mathbf A}$ (251); measure $\mathbf B$, obtaining $e$, and compute $\hat u=\mathrm{Recover}(G,e)$; apply $|x\rangle_{\mathbf A}\mapsto(-1)^{\hat u\cdot C(x)}|x\rangle_{\mathbf A}$ and output $\mathbf A$.
--
--   The definition also fixes the key-averaged channel $\mathbb E_{\mathsf{sk}}\,\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal N\circ\mathrm{Enc}_{\mathsf{sk}}$, the object of Theorem 8.17.
--
--   **Formalization Note** Everything is indexed by $n$ with $n_P=2n$. GraphSample and Recover are machines `GS`, `Rec` in the form of the base mission's `GraphRecoverSpec`: the graph is decoded from `GS(1^n, 1^{t(2n)}; r)`, and $\hat u$ is the first $2n$ bits of `Rec(1^{t(2n)}, GS(…), e)` (zero beyond the end of the output). The decoder is written as the channel $\rho\mapsto\sum_e K_e\rho K_e^\dagger$.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §8.5 and Construction 8.16, Eqs. (248)-(251), pp.63-64

import Mathlib
import Definitions.Def_QuantumPRC_GraphRecoverSpec
import Definitions.Def_QuantumPRC_graphUnitary

open Matrix

namespace QuantumPRC.Supplement

/-- **Ingredients of Construction 8.16 (keyed CWS code).** Hsieh, Yamada, arXiv:2609.38986 (version
of October 29, 2026, sha256 6901b59d…), §8.5, p.63: "Let `nP` range over even positive integers, and
let `nL = nL(nP)`. […] Let `C : {0,1}^{nL} → {0,1}^{nP}` be an injective classical encoder with a
deterministic decoder `D : {0,1}^{nP} → {0,1}^{nL}` […]. Use GraphSample and Recover from Theorem 7.1
with constant `p` and radius function `m ↦ t(2m)`."

Everything is indexed by `n` with `nP = 2n`: `nL n` is the number of logical qubits at `nP = 2n`,
`C n`, `D n` are the encoder and decoder there, and `t` is the radius as a function of `nP` (used at
`t(2n)`). GraphSample and Recover are machines `GS`, `Rec` with `gc(n)` coins, in the form of
`QuantumPRC.GraphRecoverSpec`: the sampled graph is `graphOfCode (2n) (GS(1^n, 1^{t(2n)}; r))`, and
`Recover(G, e)` is `Rec(1^{t(2n)}, GS(1^n, 1^{t(2n)}; r), e)`. -/
structure C816 where
  nL : ℕ → ℕ
  t : ℕ → ℕ
  C : ∀ n, Bits (nL n) → Bits (2 * n)
  D : ∀ n, Bits (2 * n) → Bits (nL n)
  gc : ℕ → ℕ
  GS : List Bool → List Bool
  Rec : List Bool → List Bool

namespace C816

variable (K : C816)

/-- **Secret key** of Construction 8.16, p.64: `sk = (G, P)`, given by GraphSample's coins
`r ∈ {0,1}^{gc(n)}` and an element `P` of the Pauli group `P_{nP}`. -/
abbrev Key (n : ℕ) : Type := Bits (K.gc n) × PauliIdx (2 * n)

/-- The output of `GraphSample(1^{nP/2})` on coins `r`, at radius `t(nP)`, as an adjacency code. -/
def graphCode (n : ℕ) (r : Bits (K.gc n)) : List Bool :=
  K.GS (tupleCode [unary n, unary (K.t (2 * n)), bits r])

/-- The sampled graph `G` on `[nP] = [2n]`. -/
def graph (n : ℕ) (r : Bits (K.gc n)) : SimpleGraph (Fin (2 * n)) :=
  graphOfCode (2 * n) (K.graphCode n r)

instance (n : ℕ) (r : Bits (K.gc n)) : DecidableRel (K.graph n r).Adj := by
  unfold graph; infer_instance

/-- `û = Recover(G, e)`: the first `2n` bits of Recover's output (`0` beyond its end). -/
def recover (n : ℕ) (r : Bits (K.gc n)) (e : Bits (2 * n)) : Bits (2 * n) :=
  fun i => (K.Rec (tupleCode [unary (K.t (2 * n)), K.graphCode n r, bits e])).getD i.val false

/-- `V_C : |x⟩ ↦ |C(x)⟩`, Eq. (250). -/
def vC (n : ℕ) : Matrix (Bits (2 * n)) (Bits (K.nL n)) ℂ :=
  fun y x => if y = K.C n x then 1 else 0

/-- **Enc of Construction 8.16**, p.64: `Enc_sk = P U_G V_C`. -/
noncomputable def encIso (n : ℕ) (sk : K.Key n) : Matrix (Bits (2 * n)) (Bits (K.nL n)) ℂ :=
  pauliOp sk.2 * graphUnitary (K.graph n sk.1) * K.vC n

/-- The isometry (251) from `B` to `B ⊗ A`: `|y⟩_B |0^{nL}⟩_A ↦ |y ⊕ C(D(y))⟩_B |D(y)⟩_A`. Output index
`(B, A)`. -/
def coherentDecode (n : ℕ) : Matrix (Bits (2 * n) × Bits (K.nL n)) (Bits (2 * n)) ℂ :=
  fun q y => if q.2 = K.D n y ∧ q.1 = xorB y (K.C n (K.D n y)) then 1 else 0

/-- **Dec of Construction 8.16**, p.64: "1. Apply `U_G† P†` to the received register `B`. 2. Append a
register `A` of `nL` qubits initialized to zero and coherently apply
`|y⟩_B |0^{nL}⟩_A ↦ |y ⊕ C(D(y))⟩_B |D(y)⟩_A`. (251) 3. Measure `B` in the computational basis to obtain
`e`, and compute `û = Recover(G, e)`. 4. Apply `|x⟩_A ↦ (−1)^{û·C(x)} |x⟩_A` and output `A`." As a
channel, `Dec_sk(ρ) = Σ_e K_e ρ K_e†` with
`K_e = Φ_{û(e)} (⟨e|_B ⊗ I_A) W_{(251)} U_G† P†` and `Φ_u |x⟩ = (−1)^{u·C(x)} |x⟩`. -/
noncomputable def decCh (n : ℕ) (sk : K.Key n) : Superop (Bits (2 * n)) (Bits (K.nL n)) :=
  fun ρ =>
    let Wm := K.coherentDecode n * ((graphUnitary (K.graph n sk.1))ᴴ * (pauliOp sk.2)ᴴ)
    ∑ e : Bits (2 * n),
      let Ke : Matrix (Bits (K.nL n)) (Bits (2 * n)) ℂ := fun a y =>
        (if dotB (K.recover n sk.1 e) (K.C n a) then -1 else 1) * Wm (e, a) y
      Ke * ρ * Keᴴ

/-- `𝔼_{sk←KeyGen(1^{nP})} (Dec_sk ∘ N ∘ Enc_sk)` at `nP = 2n`: KeyGen samples `G ← GraphSample(1^{nP/2})`
(uniform coins `r`) "and an independent `P ← P_{nP}`" (uniform over the `4^{nP+1}` elements). -/
noncomputable def avgDecNEnc (n : ℕ) (N : Superop (Bits (2 * n)) (Bits (2 * n))) :
    Superop (Bits (K.nL n)) (Bits (K.nL n)) :=
  fun ρ => ((Fintype.card (K.Key n) : ℂ))⁻¹ •
    ∑ sk : K.Key n, K.decCh n sk (N (conjMap (K.encIso n sk) ρ))

end C816

end QuantumPRC.Supplement


