-- Prove2me | Definitions.Def_MFHeisGibbs_KMS
-- name    : MFHeisGibbs_KMS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:19.831344+00:00
-- url     : https://prove2.me/theorems/f8e275ad-3a49-44cd-9e01-1e29bad2648a
-- title:
--   The Gibbs state $\rho^a$, KMS inner product, Dirichlet form $\mathcal E$, variance, sector gap and discriminant
-- statement:
--   At inverse temperature $\beta<\infty$, $\rho=e^{-\beta H_n}/Z_{n,\beta}$ with $Z_{n,\beta}=\mathrm{Tr}\,e^{-\beta H_n}$. The KMS inner product and related quantities are
--
--   $$\langle X,Y\rangle_\rho=\mathrm{Tr}(\rho^{1/2}X^\dagger\rho^{1/2}Y),\quad\mathcal E(X)=\langle X,-\mathcal L[X]\rangle_\rho,\quad\mathrm{Var}_\rho(X)=\|X-\mathrm{Tr}(\rho X)I\|_\rho^2 .$$
--
--   For a subspace $V$, the sector gap is
--
--   $$\gamma(\mathcal L,V)=\inf_{X\in V,\ \mathrm{Var}_\rho(X)>0}\frac{\mathcal E(X)}{\mathrm{Var}_\rho(X)},$$
--
--   and the discriminant is $\mathcal D[\cdot]=\rho^{1/4}\mathcal L[\rho^{-1/4}\cdot\rho^{-1/4}]\rho^{1/4}$.
--
--   These quantities carry all the comparison arguments of the paper.
--
--   **Formalization Note** The powers are $\rho^a=Z^{-a}e^{-a\beta H_n}$. $\|X\|^2_\rho$ and $\mathcal E(X)$ are written as real parts.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (2), p.3 (PDF 4); (13), p.5 (PDF 6); (24), p.8 (PDF 9); (27), (28), p.9 (PDF 10); (120), p.51 (PDF 52)

import Definitions.Def_MFHeisGibbs_Model

open Matrix

namespace MFHeisGibbs

/-!
# The Gibbs state, the KMS inner product, the Dirichlet form and the sector gap

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(2), p.3; (13), p.5; (24), p.8; (27), (28), p.9; pp.50–51.

**Formalization Note.** These are for finite `β`. Real powers are `ρ^a = Z^{−a} e^{−aβH_n}`, the
spectral powers of (2), with `Z = Tr e^{−βH_n} > 0`. The quantities `∥X∥²_ρ` and `⟨X, −L[X]⟩_ρ` are
taken as real parts, which they are for a KMS self-adjoint `L`. `sectorGap` is the infimum of the
Rayleigh quotient of (27) restricted to `V`, which is the sense of p.51, (120).
-/

/-- The partition function `Z_{n,β} = Tr e^{−βH_n}`, (2). -/
noncomputable def partition (β : ℝ) (n : ℕ) : ℝ :=
  (trace (NormedSpace.exp ((-(β : ℂ)) • Hn n))).re

/-- The power `ρ^a`, `ρ = ρ_{n,β} = e^{−βH_n}/Z_{n,β}`, (2). -/
noncomputable def rhoPow (β a : ℝ) (n : ℕ) : Op n :=
  ((partition β n ^ (-a) : ℝ) : ℂ) • NormedSpace.exp ((-((a * β : ℝ) : ℂ)) • Hn n)

/-- The KMS inner product `⟨X, Y⟩_ρ = Tr(ρ^{1/2} X† ρ^{1/2} Y)`, p.3. -/
noncomputable def kmsInner {n : ℕ} (β : ℝ) (X Y : Op n) : ℂ :=
  trace (rhoPow β (1 / 2) n * Xᴴ * rhoPow β (1 / 2) n * Y)

/-- The squared KMS norm `∥X∥²_ρ = ⟨X, X⟩_ρ`, p.3. -/
noncomputable def kmsNormSq {n : ℕ} (β : ℝ) (X : Op n) : ℝ := (kmsInner β X X).re

/-- The Dirichlet form `E(X) = ⟨X, −L[X]⟩_ρ`, (24). -/
noncomputable def dirichlet {n : ℕ} (β : ℝ) (L : Module.End ℂ (Op n)) (X : Op n) : ℝ :=
  (kmsInner β X (-(L X))).re

/-- The variance `Var_ρ(X) = ∥X − Tr(ρX) I∥²_ρ`, (28). -/
noncomputable def gibbsVar {n : ℕ} (β : ℝ) (X : Op n) : ℝ :=
  kmsNormSq β (X - trace (rhoPow β 1 n * X) • (1 : Op n))

/-- The sector gap `γ(L, V) = inf_{X ∈ V, Var_ρ(X) > 0} E(X)/Var_ρ(X)`, (27), p.51. -/
noncomputable def sectorGap {n : ℕ} (β : ℝ) (L : Module.End ℂ (Op n)) (V : Set (Op n)) : ℝ :=
  sInf {r : ℝ | ∃ X ∈ V, 0 < gibbsVar β X ∧ r = dirichlet β L X / gibbsVar β X}

/-- The discriminant `D[·] = ρ^{1/4} L[ρ^{−1/4} · ρ^{−1/4}] ρ^{1/4}`, (13). -/
noncomputable def discriminant {n : ℕ} (β : ℝ) (L : Module.End ℂ (Op n)) : Module.End ℂ (Op n) :=
  conjMap (rhoPow β (1 / 4) n) (rhoPow β (1 / 4) n) ∘ₗ L ∘ₗ
    conjMap (rhoPow β (-(1 / 4)) n) (rhoPow β (-(1 / 4)) n)

end MFHeisGibbs


