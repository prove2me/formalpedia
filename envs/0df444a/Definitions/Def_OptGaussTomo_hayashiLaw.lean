-- Prove2me | Definitions.Def_OptGaussTomo_hayashiLaw
-- name    : OptGaussTomo_hayashiLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:43.469618+00:00
-- url     : https://prove2.me/theorems/8d67827e-dc95-469b-aeb4-99b9023f8636
-- title:
--   Outcome law of the fermionic Gaussian Hayashi measurement $\mu_{n,m}$, eq. (C.7)
-- statement:
--   The Gaussian Hayashi measurement on $n$ copies of $m$ fermionic modes is
--
--   $$
--   d\mu^\pm_{n,m}(\phi)=d_{n,m}\,d\phi\,|\phi\rangle\langle\phi|^{\otimes n},\qquad \phi\in\mathcal G^\pm_m, \tag{C.7}
--   $$
--
--   with $d\phi$ the invariant probability measure on $\mathcal G^\pm_m$; $\mu_{n,m}$ combines both parities. On an $n$-copy input $\rho$ its outcome $\hat\psi$ has the law $\operatorname{tr}[d\mu_{n,m}(\phi)\rho]=d_{n,m}\langle\phi^{\otimes n}|\rho|\phi^{\otimes n}\rangle\,d\phi$. An outcome is recorded as a pair $(s,U)$ of a parity and a Gaussian unitary, standing for $\hat\psi=U\psi^s$; the law has density $d_{n,m}\langle (U\psi^s)^{\otimes n}|\rho|(U\psi^s)^{\otimes n}\rangle$ with respect to counting measure on parities times the Haar probability measure on Gaussian unitaries.
--
--   **Formalization Note** Only the outcome law is defined; Lemma C.5 and Corollary C.6 concern the outcome distribution on inputs $\psi^{\otimes n}$, which lie in $\mathcal V^+_{n,m}\oplus\mathcal V^-_{n,m}$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.3 p.37 (pdf p.37), eq. (C.7)

import Mathlib
import Definitions.Def_OptGaussTomo_vecPow
import Definitions.Def_OptGaussTomo_dFermi
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_fermiHaar

open FermiCap.Gaussian (Qubits Op)
open MeasureTheory

noncomputable section

namespace OptGaussTomo

/-!
# The fermionic Gaussian Hayashi measurement `μ_{n,m}`, eq. (C.7)

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.3, p.37:
"`μ^±_{n,m}`, defined by `dμ^±_{n,m}(ϕ) = d_{n,m} dϕ |ϕ⟩⟨ϕ|^{⊗n}`, (C.7) is a POVM on `V^±_{n,m}` with
outcomes in `G^±_m` … Clearly, we can combine `μ^±_{n,m}` into a single POVM `μ_{n,m}` on
`V⁺_{n,m} ⊕ V⁻_{n,m}` with outcomes in `G_m`." The outcome law on an input `ρ` is
`tr[dμ_{n,m}(ϕ) ρ]` (p.40).

An outcome is a pair `(s, U)` of a parity `s` and a Gaussian unitary `U`, standing for the
estimate `ϕ = U ψ_s ∈ G^s_m` (`ψ_s = gaussRef m s`). `hayashiLaw n m ρ` is the outcome law of
`μ_{n,m}` on the `n`-copy input `ρ`: it has density
`d_{n,m} ⟨ϕ^{⊗n}| ρ |ϕ^{⊗n}⟩` with respect to `(counting on parities) × (Haar on U)`.

**Formalization Note.** The source's `dϕ` on `G^±_m` is the push-forward of the Haar probability
measure `fermiHaar m` under `U ↦ U ψ_±` (it is invariant under Gaussian unitaries, which act
transitively), so this is (C.7) with `tr[|ϕ⟩⟨ϕ|^{⊗n} ρ] = ⟨ϕ^{⊗n}|ρ|ϕ^{⊗n}⟩`. Only the law
(not the effects) is defined; the statements about `μ_{n,m}` (Lemma C.5, Corollary C.6) concern its
outcome distribution on inputs `ψ^{⊗n}` in `V⁺_{n,m} ⊕ V⁻_{n,m}`. The real part is taken because
the quadratic form is real for Hermitian `ρ`; `ENNReal.ofReal` clips negative values, which do
not occur for positive `ρ`.
-/

/-- The outcome law of the Hayashi measurement `μ_{n,m}` on an `n`-copy input `ρ`. -/
def hayashiLaw (n m : ℕ) (ρ : Matrix (Fin n → Qubits m) (Fin n → Qubits m) ℂ) :
    Measure (Bool × fermiGaussGroup m) :=
  (Measure.count.prod (fermiHaar m)).withDensity fun p =>
    ENNReal.ofReal (dFermi n m *
      (star (vecPow n ((p.2 : Op m).mulVec (gaussRef m p.1))) ⬝ᵥ
        ρ.mulVec (vecPow n ((p.2 : Op m).mulVec (gaussRef m p.1)))).re)

end OptGaussTomo


