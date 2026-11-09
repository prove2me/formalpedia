-- Prove2me | Definitions.Def_WeldedPath_exactCpO
-- name    : WeldedPath_exactCpO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:07:13.969277+00:00
-- url     : https://prove2.me/theorems/89543e99-c05c-4dbb-8b26-8f10f9741faf
-- title:
--   Levels, the intertwiner $\mathcal I_s$ and the exact compressed query $\widehat{\mathrm{cpO}}_x$
-- statement:
--   On the permutation register $\mathcal H(\mathrm{Sym}(s))$ let $|T_I\rangle=((s-|I|)!)^{-1/2}\sum_{\phi\succeq I}|\phi\rangle$, $\mathcal H_{s,\le r}=\mathrm{Span}\{|T_I\rangle:|I|=r\}$, and **level** $r$ be $\mathcal H_{s,r}=\mathcal H_{s,\le r}\ominus\mathcal H_{s,\le r-1}$ with projector $\Pi_{s,r}$. On databases of size $r$ define $\Gamma_{s,r}|I\rangle=\Pi_{s,r}|T_I\rangle$ and $G_{s,r}=\Gamma_{s,r}\Gamma_{s,r}^\dagger$. The **intertwiner** is
--   $$
--   \mathcal I_s=\bigoplus_{r<s}\Gamma_{s,r}^\dagger G_{s,r}^{-1/2},
--   $$
--   an isometry from the permutation register to the database register. With $O_x|a,\phi\rangle=|a\oplus\phi(x),\phi\rangle$ (inverse: $\phi^{-1}(x)$) and $\Pi_{K_s}=\mathcal I_s\mathcal I_s^\dagger$, the **exact compressed query** is
--   $$
--   \widehat{\mathrm{cpO}}_x=\mathcal I_s O_x\mathcal I_s^\dagger+(1-\Pi_{K_s})\,\mathrm{cpO}_x\,(1-\Pi_{K_s}).
--   $$
--
--   It reproduces the standard oracle exactly on the range of $\mathcal I_s$ and agrees with $\mathrm{cpO}_x$ elsewhere.
--
--   **Formalization Note** $G_{s,r}^{-1/2}$ is the continuous functional calculus of $x\mapsto(\sqrt x)^{-1}$, which is $0$ at $0$; since $G_{s,r}$ vanishes off level $r$ and $G_{s,r}\succeq\Pi_{s,r}$ there, this is the inverse square root on level $r$ extended by $0$. $\mathcal I_s$ acts as the identity on the answer register.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §2.1, p.12, (10)–(14)

import Mathlib
import Definitions.Def_WeldedPath_cpO

namespace WeldedPath

open InjDb

variable {s : ℕ}

/-- `|T_I⟩ = ((s − |I|)!)^{-1/2} Σ_{ϕ ⪰ I} |ϕ⟩`, the uniform superposition over the permutations
extending `I` (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, arXiv:2611.05912
(sha256 b31400a0…), p.12). -/
noncomputable def completion (I : InjDb s) : Hil (Equiv.Perm (Fin s)) :=
  ((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) •
    ∑ ϕ ∈ Finset.univ.filter (fun ϕ : Equiv.Perm (Fin s) => Extends ϕ I), ket ϕ

/-- `H_{s,≤r} = Span{|T_I⟩ : I ∈ I_s, |I| = r}` (arXiv:2611.05912 (sha256 b31400a0…), p.12). -/
noncomputable def Hle (s r : ℕ) : Submodule ℂ (Hil (Equiv.Perm (Fin s))) :=
  Submodule.span ℂ {v | ∃ I : InjDb s, I.size = r ∧ v = completion I}

/-- Level `r`: `H_{s,r} = H_{s,≤r} ⊖ H_{s,≤r−1}`, with `H_{s,≤−1} = 0` (arXiv:2611.05912
(sha256 b31400a0…), p.12). -/
noncomputable def Hlevel (s : ℕ) : ℕ → Submodule ℂ (Hil (Equiv.Perm (Fin s)))
  | 0 => Hle s 0
  | r + 1 => Hle s (r + 1) ⊓ (Hle s r)ᗮ

/-- The projector `Π_{s,r}` onto level `r` (arXiv:2611.05912 (sha256 b31400a0…), p.12). -/
noncomputable def projLevel (s r : ℕ) :
    Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  (Hlevel s r).starProjection

/-- `Γ_{s,r}|I⟩ = Π_{s,r}|T_I⟩` on the databases of size `r` (10) (arXiv:2611.05912
(sha256 b31400a0…), p.12).

**Formalization Note.** The source's `Γ_{s,r}` has domain the span of `{|I⟩ : |I| = r}`; here it is
extended by `0` to `H(I_s)`. -/
noncomputable def Gam (s r : ℕ) : Hil (InjDb s) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.size = r),
    ketBra (projLevel s r (completion I)) (ket I)

/-- `G_{s,r} = Γ_{s,r} Γ_{s,r}^†` (10) (arXiv:2611.05912 (sha256 b31400a0…), p.12). -/
noncomputable def Gram (s r : ℕ) : Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  (Gam s r).comp (ContinuousLinearMap.adjoint (Gam s r))

/-- `G_{s,r}^{-1/2}` on level `r`, extended by `0` (arXiv:2611.05912 (sha256 b31400a0…), (12),
p.12).

**Formalization Note.** `G_{s,r}` vanishes off `H_{s,r}` and `G_{s,r} ⪰ Π_{s,r}` (p.12, Lemma 4.9
of [CM26]), so `G_{s,r}^{-1/2}` on `H_{s,r}` is the functional calculus of `x ↦ (√x)^{-1}`, whose
value `0` at `0` extends it by `0`. -/
noncomputable def GramInvSqrt (s r : ℕ) :
    Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Gram s r)

/-- The intertwiner `I_s = ⨁_{r<s} Γ_{s,r}^† G_{s,r}^{-1/2}` (12), from the permutation register `P`
to the database register `I` (arXiv:2611.05912 (sha256 b31400a0…), p.12).

**Formalization Note.** The direct sum over the levels is `Σ_{r<s} Γ_{s,r}^† G_{s,r}^{-1/2}`, each
term vanishing off level `r`. -/
noncomputable def intertwiner (s : ℕ) : Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (InjDb s) :=
  ∑ r ∈ Finset.range s, (ContinuousLinearMap.adjoint (Gam s r)).comp (GramInvSqrt s r)

/-- The standard query `O_x|a, ϕ⟩_{YP} = |a ⊕ ϕ(x), ϕ⟩_{YP}` (`inv = false`) and its inverse
`|a, ϕ⟩ ↦ |a ⊕ ϕ^{-1}(x), ϕ⟩` (`inv = true`) on the answer register and the permutation register
(arXiv:2611.05912 (sha256 b31400a0…), p.12; directions p.10). -/
noncomputable def stdQuery (d : ℕ) (x : Fin s) (inv : Bool) :
    Hil (QAlgorithms.Qubits d × Equiv.Perm (Fin s)) →L[ℂ]
      Hil (QAlgorithms.Qubits d × Equiv.Perm (Fin s)) :=
  basisMap fun p => (p.1 + encode d (if inv then p.2.symm x else p.2 x), p.2)

/-- The exact compressed permutation query (14) (arXiv:2611.05912 (sha256 b31400a0…), p.12):
`ĉpO_x = I_s O_x I_s^† + (1 − Π_{K_s}) cpO_x (1 − Π_{K_s})`, `Π_{K_s} = I_s I_s^†`, for a forward
(`inv = false`) or inverse (`inv = true`) query; `I_s` acts as the identity on the answer
register. -/
noncomputable def exactCpO (d : ℕ) (x : Fin s) (inv : Bool) :
    Hil (QAlgorithms.Qubits d × InjDb s) →L[ℂ] Hil (QAlgorithms.Qubits d × InjDb s) :=
  let Is : Hil (QAlgorithms.Qubits d × Equiv.Perm (Fin s)) →L[ℂ]
      Hil (QAlgorithms.Qubits d × InjDb s) := opTensor 1 (intertwiner s)
  let piK := Is.comp (ContinuousLinearMap.adjoint Is)
  Is.comp ((stdQuery d x inv).comp (ContinuousLinearMap.adjoint Is)) +
    (1 - piK).comp ((cpO d x inv).comp (1 - piK))

end WeldedPath


