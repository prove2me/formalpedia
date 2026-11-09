-- Prove2me | Definitions.Def_ChanTomoNB_isoDiscrimination
-- name    : ChanTomoNB_isoDiscrimination
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:41.140309+00:00
-- url     : https://prove2.me/theorems/758fa58e-4059-4ebb-ae53-f36f4c829b24
-- title:
--   Isometry discrimination with a Haar mask: $V_{P,U}=I_{d-d'}\oplus W_PU$, $X_{P,\ell}$, $X_\ell$, $\Gamma_P$, $\Gamma$ and the success probability
-- statement:
--   Let $d<D<2d$, $\alpha=D-d$ and $1\le d'\le d$, and decompose $\mathbb C^d=\mathbb C^{d-d'}\oplus\mathbb C^{d'}$ and $\mathbb C^D=\mathbb C^{d-d'}\oplus\mathbb C^{d'+\alpha}$. For an isometry $W_P:\mathbb C^{d'}\to\mathbb C^{d'+\alpha}$ with $W_PW_P^\dagger=P\in\mathrm{Proj}_{d'}(d'+\alpha)$ and $U\in\mathbb U_{d'}$:
--
--   1. $V_{P,U}=I_{d-d'}\oplus W_PU:\mathbb C^d\to\mathbb C^D$;
--   2. $X_{P,\ell}=\mathbb E_{U\sim\mathbb U_{d'}}|W_PU\rangle\!\rangle\langle\!\langle W_PU|^{\otimes\ell}$ and $X_\ell=\mathbb E_{P\sim\mathrm{Proj}_{d'}(d'+\alpha)}X_{P,\ell}$;
--   3. $\Gamma_P=\mathbb E_{U\sim\mathbb U_{d'}}C_{V_{P,U}}^{\otimes n}$ and $\Gamma=\mathbb E_{P\sim\mathrm{Proj}_{d'}(d'+\alpha)}\Gamma_P$, with $C_V=|V\rangle\!\rangle\langle\!\langle V|$;
--   4. for a finite set $\mathcal N$ of projectors, a tester on $(\mathbb C^d,\mathbb C^D)$ and a guess $g(i)$ for each outcome $i$, the **success probability** in Problem 4.1 is
--   $$
--   \mathbb P[\mathrm{success}]=\frac1{|\mathcal N|}\sum_{P\in\mathcal N}\ \mathbb E_{U\sim\mathbb U_{d'}}\sum_{i:\ g(i)=P}p_i\big(V_{P,U}\big).
--   $$
--
--   Problem 4.1: the referee draws $P\in\mathcal N$ uniformly and an independent Haar $U$, and the learner, with queries to $V_{P,U}$, must identify $P$.
--
--   **Formalization Note** Expectations are entrywise Bochner integrals against the normalized Haar measure; $P\sim\mathrm{Proj}_{d'}(d'+\alpha)$ is $P=U'P_0U'^\dagger$ with $W_P=U'W_0$ (p.24). $C_V^{\otimes n}$ is written on the tester's order of tensor factors. The sum over outcomes and the Haar expectation are exchanged (nonnegative terms).
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §4, Eq. (45), Problem 4.1, p.21; Eqs. (46)–(47), p.22; Lemma 4.4, p.23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_Proj

open Matrix MeasureTheory

namespace ChanTomoNB

/-- The isometry `V_{P,U} := I_{d−d′} ⊕ W_P U : ℂ^d → ℂ^D` of §4, built from an isometry
`Wm = W_P U : ℂ^{d′} → ℂ^{d′+α}`. Chen, Oufkir, *Quantum channel tomography: optimal bounds in
the near-boundary regime*, arXiv:2611.03639v1, §4, Eq. (45), p.21.

**Formalization Note.** The input and output spaces are written in the decomposition (45):
`ℂ^d = ℂ^{d−d′} ⊕ ℂ^{d′}` is `Fin d0 ⊕ Fin d′` and `ℂ^D = ℂ^{d−d′} ⊕ ℂ^{d′+α}` is
`Fin d0 ⊕ Fin (d′+α)`, with `d0 = d − d′`. -/
def V4 {d0 d' α : ℕ} (Wm : Matrix (Fin (d' + α)) (Fin d') ℂ) :
    Matrix (Fin d0 ⊕ Fin (d' + α)) (Fin d0 ⊕ Fin d') ℂ :=
  Matrix.fromBlocks 1 0 0 Wm

/-- `|X⟩⟩⟨⟨X|^{⊗ℓ}` for `X : ℂ^k → ℂ^m`, with `|X⟩⟩ ∈ ℂ^m ⊗ ℂ^k` the flattening of `X`
(arXiv:2611.03639v1, §2.1, p.9). Indexed by `Fin ℓ → (Fin m × Fin k)`. -/
def vecPow {m k : Type} (X : Matrix m k ℂ) (ℓ : ℕ) :
    Matrix (Fin ℓ → m × k) (Fin ℓ → m × k) ℂ :=
  Matrix.of fun x y => ∏ j, X (x j).1 (x j).2 * star (X (y j).1 (y j).2)

/-- `X_{P,ℓ} = E_{U∼U_{d′}} |W_P U⟩⟩⟨⟨W_P U|^{⊗ℓ}` for the isometry `Wp = W_P`
(arXiv:2611.03639v1, Lemma 4.4, p.23).

**Formalization Note.** The expectation over the Haar probability measure
(`QAlgorithms.Schur.unitaryHaar`) is taken entrywise. -/
noncomputable def XP {d' α : ℕ} (ℓ : ℕ) (Wp : Matrix (Fin (d' + α)) (Fin d') ℂ) :
    Matrix (Fin ℓ → Fin (d' + α) × Fin d') (Fin ℓ → Fin (d' + α) × Fin d') ℂ :=
  Matrix.of fun x y =>
    ∫ U, vecPow (Wp * (U : Matrix (Fin d') (Fin d') ℂ)) ℓ x y ∂(QAlgorithms.Schur.unitaryHaar d')

/-- `X_ℓ = E_{P∼Proj_{d′}(d′+α)} X_{P,ℓ}` (arXiv:2611.03639v1, Lemma 4.4, p.23).

**Formalization Note.** `P ∼ Proj_{d′}(d′+α)` is `P = U′ P₀ U′†` with `U′ ∼ U_{d′+α}` (p.24), and
`W_P = U′ W₀` is an isometry with `W_P W_P† = P`. `X_{P,ℓ}` does not depend on the choice of
`W_P` (two choices differ by a unitary on `ℂ^{d′}`, absorbed by the Haar measure). -/
noncomputable def Xl (d' α ℓ : ℕ) :
    Matrix (Fin ℓ → Fin (d' + α) × Fin d') (Fin ℓ → Fin (d' + α) × Fin d') ℂ :=
  Matrix.of fun x y =>
    ∫ U', XP ℓ ((U' : Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ) * W0 d' (d' + α)) x y
      ∂(QAlgorithms.Schur.unitaryHaar (d' + α))

/-- `Γ_P := E_{U∼U_{d′}} C_{V_{P,U}}^{⊗n}` (arXiv:2611.03639v1, Eq. (46), p.22), for the isometry
`Wp = W_P`, written on the tester's space (`choiPow`).

**Formalization Note.** `C_{V}` is the Choi operator of the isometry channel `X ↦ V X V†`, that is
`|V⟩⟩⟨⟨V|`. The expectation is entrywise. -/
noncomputable def GammaP {d0 d' α : ℕ} (n : ℕ) (Wp : Matrix (Fin (d' + α)) (Fin d') ℂ) :
    Matrix (Fin n → (Fin d0 ⊕ Fin d') × (Fin d0 ⊕ Fin (d' + α)))
      (Fin n → (Fin d0 ⊕ Fin d') × (Fin d0 ⊕ Fin (d' + α))) ℂ :=
  Matrix.of fun x y =>
    ∫ U, choiPow (isoChan (V4 (d0 := d0) (Wp * (U : Matrix (Fin d') (Fin d') ℂ)))) n x y
      ∂(QAlgorithms.Schur.unitaryHaar d')

/-- `Γ := E_{P∼Proj_{d′}(d′+α)} Γ_P` (arXiv:2611.03639v1, Eq. (47), p.22), with
`P = U′ P₀ U′†`, `W_P = U′ W₀`, `U′ ∼ U_{d′+α}` (see `Xl`). -/
noncomputable def Gamma (d0 d' α n : ℕ) :
    Matrix (Fin n → (Fin d0 ⊕ Fin d') × (Fin d0 ⊕ Fin (d' + α)))
      (Fin n → (Fin d0 ⊕ Fin d') × (Fin d0 ⊕ Fin (d' + α))) ℂ :=
  Matrix.of fun x y =>
    ∫ U', GammaP (d0 := d0) n ((U' : Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ) * W0 d' (d' + α)) x y
      ∂(QAlgorithms.Schur.unitaryHaar (d' + α))

open Classical in
/-- The success probability in Problem 4.1 (arXiv:2611.03639v1, p.21) of an `n`-query tester `T`
on `(ℂ^d, ℂ^D)` that outputs the guess `g i` on outcome `i`: the referee draws `P ∈ N` uniformly
and an independent Haar `U ∼ U_{d′}`, and the tester queries `V_{P,U}`; success is `g i = P`.
`W P` is the fixed isometry `W_P` with `W_P W_P† = P`.

**Formalization Note.** `P[success] = |N|⁻¹ ∑_{P∈N} ∑'_i [g i = P] E_U p_i(V_{P,U})`; the sum over
outcomes and the Haar expectation are exchanged (Tonelli, nonnegative terms). A tester whose
outcomes are `N` itself (`{T_P}_{P∈N}`, p.22) is the case `g = id`. -/
noncomputable def discrimSuccess {d0 d' α n : ℕ}
    (T : Tester (Fin d0 ⊕ Fin d') (Fin d0 ⊕ Fin (d' + α)) n)
    (N : Finset (Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ))
    (W : Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ → Matrix (Fin (d' + α)) (Fin d') ℂ)
    (g : T.ι → Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ) : ℝ :=
  (1 / (N.card : ℝ)) * ∑ P ∈ N, ∑' i, if g i = P then
    ∫ U, T.prob (isoChan (V4 (d0 := d0) (W P * (U : Matrix (Fin d') (Fin d') ℂ)))) i
      ∂(QAlgorithms.Schur.unitaryHaar d') else 0

end ChanTomoNB


