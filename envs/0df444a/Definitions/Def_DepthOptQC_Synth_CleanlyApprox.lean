-- Prove2me | Definitions.Def_DepthOptQC_Synth_CleanlyApprox
-- name    : DepthOptQC_Synth_CleanlyApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:35.793195+00:00
-- url     : https://prove2.me/theorems/b1e0040c-770f-463c-9137-cd6c36292114
-- title:
--   Clean $\varepsilon$-approximation of a single-qubit unitary with one global phase
-- statement:
--   Let $M$ be a unitary on $1+a$ qubits (one system qubit and $a$ ancillas), $U$ a single-qubit operator, $c\in\mathbb C$ and $\varepsilon\ge 0$. We say $M$ **approximates $U$ with phase factor $c$ and clean ancillas** if
--   $$
--   \big\| M(|\psi\rangle\otimes|0^a\rangle) - c\,(U|\psi\rangle\otimes|0^a\rangle)\big\| \le \varepsilon\,\|\psi\| \qquad\text{for every } |\psi\rangle\in\mathbb C^2,
--   $$
--   equivalently $\|M(I\otimes|0^a\rangle) - c\,(U\otimes|0^a\rangle)\|_{\mathrm{op}}\le\varepsilon$. We say $M$ **cleanly $\varepsilon$-approximates** $U$ if this holds with $c=e^{i\varphi}$ for one phase $\varphi\in\mathbb R$, the same for all inputs.
--
--   The ancillas start in $|0^a\rangle$ and the whole $(1+a)$-qubit output is compared with $e^{i\varphi}U|\psi\rangle\otimes|0^a\rangle$, so amplitude left on nonzero ancilla states counts as error: the ancillas are approximately restored.
--
--   **Formalization Note** The system qubit is wire $0$ and the ancillas are wires $1,\dots,a$ (the paper writes $|0^a\rangle\otimes I$ with the ancillas first; a fixed relabelling of wires). `CleanlyApproxWith M U c ε` is the fixed-phase form used with $c=-1$ ($\varphi=\pi$) in Theorem 8, Corollary 1 and Lemma 5.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 1, p.6; §1.1, p.5; Eq. (80), p.23; Eq. (102), p.26; Eqs. (106)–(107), pp.26–27

import Definitions.Def_QAlgorithms_Defs_CircuitResources

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Clean `ε`-approximation with a given phase factor** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Eq. (80), p.23; Eq. (102), p.26; Eqs. (106)–(107), pp.26–27): the
matrix `M` on `1 + a` qubits approximates the single-qubit `U` with the phase factor `c` and clean
ancillas if, for every system vector `ψ`,
`‖M (ψ ⊗ |0^a⟩) − c · (Uψ ⊗ |0^a⟩)‖ ≤ ε ‖ψ‖`.

**Formalization Note.** The system qubit is wire `0` and the `a` ancillas are wires `1, …, a`, all
starting in `|0⟩` (`QAlgorithms.zeroAncillaVec`; reading R4: the paper writes `|0^a⟩ ⊗ I`, ancillas
first). The whole `(1 + a)`-qubit output is compared, so amplitude left on the ancillas counts as
error. By homogeneity the condition is the operator-norm bound
`‖M(I ⊗ |0^a⟩) − c (U ⊗ |0^a⟩)‖_op ≤ ε` of (80) and the per-state bound of (106) (reading R6). -/
def CleanlyApproxWith {a : ℕ} (M : Matrix (Qubits (1 + a)) (Qubits (1 + a)) ℂ)
    (U : Matrix (Qubits 1) (Qubits 1) ℂ) (c : ℂ) (ε : ℝ) : Prop :=
  ∀ ψ : EuclideanSpace ℂ (Qubits 1),
    ‖act M (zeroAncillaVec ψ a) - c • zeroAncillaVec (act U ψ) a‖ ≤ ε * ‖ψ‖

/-- **Clean `ε`-approximation up to one global phase** (Vasconcelos, arXiv:2609.34659, Theorem 1,
p.6, "cleanly ε-approximates"; §1.1, p.5: "using |0⟩-initialized ancillae that are approximately
restored at the end, up to an input-independent global phase"; Eq. (107), p.27): there is one phase
`φ ∈ ℝ`, chosen before the input, with `CleanlyApproxWith M U (e^{iφ}) ε`. -/
def CleanlyApprox {a : ℕ} (M : Matrix (Qubits (1 + a)) (Qubits (1 + a)) ℂ)
    (U : Matrix (Qubits 1) (Qubits 1) ℂ) (ε : ℝ) : Prop :=
  ∃ φ : ℝ, CleanlyApproxWith M U (Complex.exp (φ * Complex.I)) ε

end DepthOptQC.Synth


