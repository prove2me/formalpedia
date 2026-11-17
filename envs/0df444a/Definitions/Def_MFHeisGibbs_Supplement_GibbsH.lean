-- Prove2me | Definitions.Def_MFHeisGibbs_Supplement_GibbsH
-- name    : MFHeisGibbs_Supplement_GibbsH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:15:41.688845+00:00
-- url     : https://prove2.me/theorems/bcf10bbd-6d56-4318-8b94-392e5a6f107c
-- title:
--   Dirichlet form, variance and sector gap for the Gibbs state of a general Hamiltonian $H$
-- statement:
--   Let $H$ be a Hamiltonian (a Hermitian matrix) on the $n$-qubit space $\mathcal H_n=(\mathbb C^2)^{\otimes n}$ and $0<\beta<\infty$. Its Gibbs state is $\rho=e^{-\beta H}/Z$ with partition function $Z=\operatorname{Tr}e^{-\beta H}$, and its real powers are $\rho^a=Z^{-a}e^{-a\beta H}$. For operators $X,Y$ on $\mathcal H_n$:
--
--   1. the KMS inner product is $\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho^{1/2}X^\dagger\rho^{1/2}Y)$;
--   2. the Dirichlet form of a generator $\mathcal L$ is $\mathcal E_{\mathcal L}(X)=\operatorname{Re}\langle X,-\mathcal L[X]\rangle_\rho$;
--   3. the variance is $\operatorname{Var}_\rho(X)=\|X-\operatorname{Tr}(\rho X)I\|_\rho^2$;
--   4. the variational gap on a set $V$ of operators is
--
--   $$\gamma(\mathcal L,V)=\inf_{X\in V,\ \operatorname{Var}_\rho(X)>0}\frac{\mathcal E_{\mathcal L}(X)}{\operatorname{Var}_\rho(X)}.$$
--
--   These are the quantities of the main text with the mean-field Hamiltonian $H_n$ replaced by an arbitrary $H$, as Appendix B requires for the gap-transfer theorem.
--
--   **Formalization Note** The Gibbs powers and the KMS inner product are the published `SysBathGibbs.gibbsPow` and `SysBathGibbs.kmsInner` (same conventions: $\rho^a=Z^{-a}e^{-a\beta H}$, $\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho^{1/2}X^\dagger\rho^{1/2}Y)$); this module adds the Dirichlet form, the variance and the gap. The norm and the Dirichlet form are real parts, which is what they are for KMS self-adjoint generators. The gap is the infimum of the restricted Rayleigh quotient, as in (120).
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (2), p.3 (PDF 4); (24), p.8 (PDF 9); (27), (28), p.9 (PDF 10); Appendix B.1, p.50 (PDF 51)

import Definitions.Def_MFHeisGibbs_Model
import Definitions.Def_SysBathGibbs_KMS

open Matrix

namespace MFHeisGibbs

namespace Supplement

/-!
# Dirichlet form, variance and sector gap for the Gibbs state of a general Hamiltonian

Raikovich, Mák, Czabán, Gilyén, *The complete phase diagram of detailed-balanced Gibbs samplers for
the mean-field Heisenberg model*, arXiv:2610.06818 (version dated November 3, 2026, sha256
164d57ba…), (2), p.3; (24), p.8; (27), (28), p.9; Appendix B.1, p.50 (PDF 51).

Appendix B replaces the mean-field `H_n` by an arbitrary Hamiltonian `H` on `H_n = (ℂ²)^{⊗n}` and uses
"the Dirichlet form, variance and variational gap of (24), (28) and (27), all with respect to the same
Gibbs state ρ" of `H`. These are the published `MFHeisGibbs.KMS` quantities with `Hn n` replaced by `H`.

**Formalization Note.** The Gibbs powers and the KMS inner product are the published
`SysBathGibbs.gibbsPow β H a = Z^{−a} e^{−aβH}` (`Z = Tr e^{−βH}`) and
`SysBathGibbs.kmsInner β H X Y = Tr(ρ^{1/2} X† ρ^{1/2} Y)`, the same conventions as (2) and p.3. These
are for finite `β`. `∥X∥²_ρ` and `⟨X, −L[X]⟩_ρ` are taken as real parts, which they are for a KMS
self-adjoint `L`. `sectorGapH` is the infimum of the Rayleigh quotient of (27) restricted to `V`, the
sense of p.51, (120); when `V` holds an observable of positive variance the set is nonempty.
-/

variable {n : ℕ}

/-- The Dirichlet form `E_L(X) = Re ⟨X, −L[X]⟩_ρ`, (24), for the Gibbs state of `H`. -/
noncomputable def dirichletH (H : Op n) (β : ℝ) (L : Module.End ℂ (Op n)) (X : Op n) : ℝ :=
  (SysBathGibbs.kmsInner β H X (-(L X))).re

/-- The variance `Var_ρ(X) = ∥X − Tr(ρX) I∥²_ρ`, (28), for the Gibbs state `ρ` of `H`. -/
noncomputable def gibbsVarH (H : Op n) (β : ℝ) (X : Op n) : ℝ :=
  (SysBathGibbs.kmsInner β H (X - trace (SysBathGibbs.gibbsPow β H 1 * X) • (1 : Op n))
    (X - trace (SysBathGibbs.gibbsPow β H 1 * X) • (1 : Op n))).re

/-- The variational gap `γ(L, V) = inf_{X ∈ V, Var_ρ(X) > 0} E_L(X)/Var_ρ(X)`, (27), p.51. -/
noncomputable def sectorGapH (H : Op n) (β : ℝ) (L : Module.End ℂ (Op n)) (V : Set (Op n)) : ℝ :=
  sInf {r : ℝ | ∃ X ∈ V, 0 < gibbsVarH H β X ∧ r = dirichletH H β L X / gibbsVarH H β X}

end Supplement

end MFHeisGibbs


