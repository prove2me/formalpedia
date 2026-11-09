-- Prove2me | Definitions.Def_ChanTomoNB_hardChannel
-- name    : ChanTomoNB_hardChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:45.453136+00:00
-- url     : https://prove2.me/theorems/b2342c14-396e-450a-8b1a-f95dad5d0d79
-- title:
--   The hard family $V_{P,U}=[F\ \ W_PU]$, $\mathcal E_{P,U}=\mathrm{tr}_{\mathrm{anc}}\circ V_{P,U}$, the law $\mu$ and the good set $\mathcal G$
-- statement:
--   In the near-boundary regime, with $d'=\lfloor d_1/2\rfloor$, $\mathcal H_{A_1}=\mathbb C^{d_1-d'}$, $\mathcal H_{A_2}=\mathbb C^{d'}$, $\mathcal H_B=\mathbb C^{d_2}$, $\mathcal H_{\mathrm{anc}}=\mathbb C^r$:
--
--   1. a **balanced reference** is an isometry $F:\mathcal H_{A_1}\to\mathcal H_B\otimes\mathcal H_{\mathrm{anc}}$ with $\operatorname{tr}_B(FF^\dagger)\succeq\lambda_0I_r$;
--   2. $\Pi=I-FF^\dagger$, and $\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$ is the set of rank-$d'$ orthogonal projectors $P$ with $\operatorname{im}P\subseteq\operatorname{im}\Pi$;
--   3. a choice $P\mapsto W_P$ of isometries $W_P:\mathbb C^{d'}\to\operatorname{im}\Pi$ with $W_PW_P^\dagger=P$;
--   4. for $U\in\mathbb U(d')$,
--   $$
--   V_{P,U}=\begin{pmatrix}F & W_PU\end{pmatrix},\qquad \mathcal E_{P,U}(X)=\operatorname{tr}_{\mathrm{anc}}\big(V_{P,U}XV_{P,U}^\dagger\big);
--   $$
--   5. $\mu$ is the law of $\Psi UP_0U^\dagger\Psi^\dagger$, $U$ Haar on $\mathbb U_{d'+\alpha}$, for an isometry $\Psi$ onto $\operatorname{im}\Pi$ (conjugation of a fixed projector by a Haar unitary);
--   6. the **good set** is $\mathcal G=\{P\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi):\operatorname{tr}_B(\Pi-P)\preceq\kappa I_r\}$.
--
--   These channels form the packing nets of the lower bound.
--
--   **Formalization Note** $\operatorname{tr}_B$ is the published `WildeQIT.partialTraceLeft` (trace over the first factor of $\mathcal H_B\otimes\mathcal H_{\mathrm{anc}}$). The input $\mathbb C^{d_1}$ is identified with $\mathcal H_{A_1}\oplus\mathcal H_{A_2}$ (first $d_1-d'$ basis vectors, then the last $d'$). $\mu(S)$ is the Haar probability of the preimage of $S$.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §5.1, Lemma 5.1 and Eq. (50), pp.25–26; Eq. (52), p.26

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_Proj
import Definitions.Def_ChanTomoNB_nearBoundaryParams

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- `F : H_{A1} → H_B ⊗ H_anc` is a balanced reference: an isometry (`F†F = I`) with
`tr_B(F F†) ⪰ λ₀ I_r`, `λ₀ = (d − d′)/(2r)`. Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.1, p.25.

**Formalization Note.** `H_{A1} = ℂ^{d1−d′}` is `Fin (d1 − d′)` (`d′ = d1/2 ≤ d1`), and
`H_B ⊗ H_anc = ℂ^{d2} ⊗ ℂ^r` is `Fin d2 × Fin r` (`H_B` first). `tr_B` is the published
`WildeQIT.partialTraceLeft` (trace over the first factor). `X ⪰ λ I` is `(X − λ I) ⪰ 0`. -/
def IsBalancedRef (d1 d2 r : ℕ) (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) : Prop :=
  Fᴴ * F = 1 ∧
    (WildeQIT.partialTraceLeft (F * Fᴴ) - ((lam0 d1 r : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef

/-- `Π = I_D − F F†`, the projector onto `(im F)^⊥ ⊆ H_B ⊗ H_anc` (arXiv:2611.03639v1, p.25). -/
def PiF {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) :
    Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ :=
  1 - F * Fᴴ

/-- `Proj_{d′}(im Π)`: the rank-`d′` orthogonal projectors `P` on `H_B ⊗ H_anc` with
`im P ⊆ im Π` (i.e. `P Π = P`), `d′ = ⌊d1/2⌋` (arXiv:2611.03639v1, §5.1, p.26). -/
def ProjIm {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) :
    Set (Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ) :=
  {P | P ∈ Proj (dp d1) (Fin d2 × Fin r) ∧ P * PiF F = P}

/-- `W` is a choice `P ↦ W_P` of isometries `W_P : ℂ^{d′} → im Π` with `W_P W_P† = P`, for every
`P ∈ Proj_{d′}(im Π)` ("For each P ∈ Proj_{d′}(im Π), fix an isometry W_P", arXiv:2611.03639v1,
p.26). -/
def IsSignalChoice {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ)
    (W : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ → Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ) :
    Prop :=
  ∀ P ∈ ProjIm F, (W P)ᴴ * W P = 1 ∧ W P * (W P)ᴴ = P

/-- The identification `ℂ^{d1} = ℂ^{d1−d′} ⊕ ℂ^{d′}` = `H_{A1} ⊕ H_{A2}` (first `d1 − d′` basis
vectors, then the last `d′`), arXiv:2611.03639v1, §5.1, p.25. -/
def inEquiv (d1 : ℕ) : Fin (d1 - dp d1) ⊕ Fin (dp d1) ≃ Fin d1 :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel (Nat.div_le_self d1 2)))

/-- `V_{P,U} := [F  W_P U] : H_{A1} ⊕ H_{A2} → H_B ⊗ H_anc` (arXiv:2611.03639v1, Eq. (50), p.26),
for `Wp = W_P` and `U ∈ U(d′)`. -/
def V5 {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ)
    (Wp : Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ) (U : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ) :
    Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1) ⊕ Fin (dp d1)) ℂ :=
  Matrix.fromCols F (Wp * U)

/-- `E_{P,U} := tr_anc ∘ V_{P,U}`, i.e. `X ↦ tr_anc(V_{P,U} X V_{P,U}†)`, as a map
`L(ℂ^{d1}) → L(ℂ^{d2})` (arXiv:2611.03639v1, Eq. (50), p.26). Its Kraus operators are
`K_e = (I_B ⊗ ⟨e|) V_{P,U}`, `e < r`; the input is identified with `H_{A1} ⊕ H_{A2}` by `inEquiv`. -/
noncomputable def E5 {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ)
    (Wp : Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ) (U : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ) :
    Superop (Fin d1) (Fin d2) :=
  krausMap fun e : Fin r => Matrix.of fun b a => V5 F Wp U (b, e) ((inEquiv d1).symm a)

/-- `Ψ` is an isometry `ℂ^{d′+α} → H_B ⊗ H_anc` onto `im Π` (`Ψ†Ψ = I`, `Ψ Ψ† = Π`); it
identifies `im Π` with `ℂ^{d′+α}` (`rank Π = d′ + α`, p.25). -/
def IsOuterIsometry {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ)
    (Ψ : Matrix (Fin d2 × Fin r) (Fin (dp d1 + alpha d1 d2 r)) ℂ) : Prop :=
  Ψᴴ * Ψ = 1 ∧ Ψ * Ψᴴ = PiF F

/-- `µ`, the invariant probability measure on `Proj_{d′}(im Π)` "obtained by conjugating a fixed
projector by a Haar unitary" (arXiv:2611.03639v1, p.26), evaluated on a set `S`:
`µ(S) = P_{U∼U_{d′+α}}[Ψ U P₀ U† Ψ† ∈ S]`, with `P₀ = diag(I_{d′}, 0_α)`.

**Formalization Note.** The fixed projector is `Ψ P₀ Ψ†` for an isometry `Ψ` onto `im Π`; the
value is the Haar (outer) measure of the preimage, which is the pushforward law on the
measurable sets used here (closed sets). -/
noncomputable def muProj {d1 d2 r : ℕ}
    (Ψ : Matrix (Fin d2 × Fin r) (Fin (dp d1 + alpha d1 d2 r)) ℂ)
    (S : Set (Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ)) : ENNReal :=
  QAlgorithms.Schur.unitaryHaar (dp d1 + alpha d1 d2 r)
    {U | Ψ * (U : Matrix (Fin (dp d1 + alpha d1 d2 r)) (Fin (dp d1 + alpha d1 d2 r)) ℂ) *
        P0 (dp d1) (dp d1 + alpha d1 d2 r) *
        (U : Matrix (Fin (dp d1 + alpha d1 d2 r)) (Fin (dp d1 + alpha d1 d2 r)) ℂ)ᴴ * Ψᴴ ∈ S}

/-- The good set `G = {P ∈ Proj_{d′}(im Π) : tr_B(Π − P) ⪯ κ I_r}`, `κ = C₀(α/r + 1/d2)`,
`C₀ = 450` (arXiv:2611.03639v1, Eq. (52), p.26). -/
def goodSet {d1 d2 r : ℕ} (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) :
    Set (Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ) :=
  {P | P ∈ ProjIm F ∧
    (((kappa d1 d2 r : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
      WildeQIT.partialTraceLeft (PiF F - P)).PosSemidef}

end ChanTomoNB


