-- Prove2me | Definitions.Def_RetroCorr_Separation_Channel
-- name    : RetroCorr_Separation_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:32.000002+00:00
-- url     : https://prove2.me/theorems/314a7da0-927d-48fc-91bf-2016b7066133
-- title:
--   Fig. 1, p. 2 — the standard retrocorrectable channel R_{c,d}: Haar flag law on (B, U₁…U_c), branch map X ↦ Σ_j U_j Tr_c[(|b_j⟩⟨b_j| ⊗ I)X] U_j†, basis B^T, ebit
-- statement:
--   The **standard retrocorrectable channel** $R_{c,d}$ of Fig. 1, for integers $c,d$ (the paper takes $c,d\ge 2$).
--
--   **Inputs and outputs.** The channel has a *control input* in $\mathbb C^c$ and a *data input* in $\mathbb C^d$; an input operator $X$ is a matrix on $\mathbb C^c\otimes\mathbb C^d$, control first. Its outputs are a *data output* in $\mathbb C^d$ and a classical *control output* (the "flag") $k=(B,U_1,\dots,U_c)$.
--
--   **The flag law.** The channel draws, independently,
--
--   1. a basis $B=\{w_1,\dots,w_c\}$ of $\mathbb C^c$, given as the columns $w_j=We_j$ of a unitary $W\in U(c)$ distributed according to the normalized Haar measure on $U(c)$;
--   2. unitaries $U_1,\dots,U_c\in U(d)$, each distributed according to the normalized Haar measure on $U(d)$.
--
--   So the flag law is $\mu_{c,d}=\mathrm{Haar}_{U(c)}\otimes\mathrm{Haar}_{U(d)}^{\otimes c}$.
--
--   **The branch for one flag value.** Given $k=(W,U_1,\dots,U_c)$, the channel measures the control in the basis $B$ (outcome $j$), applies $U_j$ to the data and does not output $j$:
--   $$\mathcal N_k(X)=\sum_{j=1}^{c}U_j\,\operatorname{Tr}_c\!\big[(|w_j\rangle\langle w_j|\otimes I_d)\,X\big]\,U_j^\dagger .$$
--
--   **Auxiliary objects of §3.** The projector $|w_j\rangle\langle w_j|$; the projectors of the basis $B^T$, namely the transposes $(|w_j\rangle\langle w_j|)^T=|\bar w_j\rangle\langle\bar w_j|$; and the maximally entangled state $\Phi_c=c^{-1/2}\sum_a|a\rangle|a\rangle$ on (reference, control), whose density matrix has entries $1/c$ at $((a,a),(b,b))$ and $0$ elsewhere. For $c=2$, $\Phi_2$ is an ebit.
--
--   These are the objects of every statement of the mission: the classical flag is part of the channel's output, and the hidden outcome $j$ never is.
--
--   **Formalization Note** The flag is the pair `(W, U)` in `Matrix.unitaryGroup (Fin c) ℂ × (Fin c → Matrix.unitaryGroup (Fin d) ℂ)`; the flag law `flagLaw c d` is the product of `QAlgorithms.Schur.unitaryHaar c` with the product measure of $c$ copies of `unitaryHaar d` (Borel σ-algebras). Indices are 0-based (`Fin c`). The basis $B$ is represented by a unitary $W$, so the phases of its columns are part of the flag; they are independent of the input and change no capacity. The paper's "random" is read as Haar: under this reading, and no other natural one, eq. (1) holds. `retroBranch c d k` is the superoperator $\mathcal N_k$, written with `QAlgorithms.traceLeft` (partial trace over the control) and `Matrix.kronecker`.
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 2, Fig. 1 and §1; p. 3, §3 (basis B^T, ebit)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RetroCorr.Separation

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Matrix

/-- Fig. 1, p. 2: the classical control output ("flag") of `R_{c,d}`: the random basis `B` of
`H_c`, represented by a unitary `W` whose columns `w_j = W e_j` are the basis vectors, together
with the `c` random unitaries `U_1, …, U_c` on `H_d`. -/
abbrev Flag (c d : ℕ) : Type :=
  Matrix.unitaryGroup (Fin c) ℂ × (Fin c → Matrix.unitaryGroup (Fin d) ℂ)

/-- Fig. 1, p. 2 ("random basis", "random unitaries"): the law of the flag. `B` (through `W`)
and `U_1, …, U_c` are independent and each is Haar distributed (the normalized Haar probability
measure `QAlgorithms.Schur.unitaryHaar` on the unitary group). -/
def flagLaw (c d : ℕ) : Measure (Flag c d) :=
  (QAlgorithms.Schur.unitaryHaar c).prod
    (Measure.pi fun _ : Fin c => QAlgorithms.Schur.unitaryHaar d)

/-- The projector `|w_j⟩⟨w_j|` onto the `j`-th vector of the basis `B` given by the columns of
`W`. -/
def basisProj {c : ℕ} (W : Matrix.unitaryGroup (Fin c) ℂ) (j : Fin c) :
    Matrix (Fin c) (Fin c) ℂ :=
  Matrix.of fun a b => (W : Matrix (Fin c) (Fin c) ℂ) a j * star ((W : Matrix (Fin c) (Fin c) ℂ) b j)

/-- §3, p. 3: the `j`-th projector of the basis `B^T`, the transpose `(|w_j⟩⟨w_j|)^T`
(`= |w̄_j⟩⟨w̄_j|`, the projector onto the complex-conjugate vector). -/
def transposeBasisProj {c : ℕ} (W : Matrix.unitaryGroup (Fin c) ℂ) (j : Fin c) :
    Matrix (Fin c) (Fin c) ℂ :=
  (basisProj W j)ᵀ

/-- Fig. 1, p. 2: the action of `R_{c,d}` for one value `k = (W, U_1, …, U_c)` of its classical
control output. The input is indexed by `(control, data)`. The channel measures the control in
the basis `B = {w_j}`, applies `U_j` to the data and forgets `j`:
`X ↦ Σ_j U_j Tr_c[(|w_j⟩⟨w_j| ⊗ I) X] U_j†`. -/
def retroBranch (c d : ℕ) (k : Flag c d) :
    QAlgorithms.Superop (Fin c × Fin d) (Fin d) :=
  fun X => ∑ j : Fin c,
    (k.2 j : Matrix (Fin d) (Fin d) ℂ) *
      QAlgorithms.traceLeft (Matrix.kronecker (basisProj k.1 j) (1 : Matrix (Fin d) (Fin d) ℂ) * X) *
      (k.2 j : Matrix (Fin d) (Fin d) ℂ)ᴴ

/-- §3, p. 3: the density matrix of the maximally entangled state
`Φ_c = c^{-1/2} Σ_a |a⟩|a⟩` on `(reference, control)`; for `c = 2` this is an ebit. -/
def maxEntDensity (c : ℕ) : Matrix (Fin c × Fin c) (Fin c × Fin c) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then ((c : ℂ))⁻¹ else 0

end

end RetroCorr.Separation


