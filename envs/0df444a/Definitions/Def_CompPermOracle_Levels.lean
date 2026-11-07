-- Prove2me | Definitions.Def_CompPermOracle_Levels
-- name    : CompPermOracle_Levels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:05.330935+00:00
-- url     : https://prove2.me/theorems/0ded6229-c435-41c7-8fc1-aa748da63a72
-- title:
--   Permutation levels $\mathcal H_r$, the frame $\Gamma_r$, Gram operators $G_r$, spaces $K_r$ and the maps $V$, $\tilde V$
-- statement:
--   For $f\in\mathcal I_r$ let $T_f=\{\varphi\in S_N:\varphi|_{\mathrm{dom}(f)}=f\}$ and let $|T_f\rangle=((N-r)!)^{-1/2}\sum_{\varphi\in T_f}|\varphi\rangle$ be the completion state. The **permutation levels** are
--   $$
--   \mathcal H_{\le r}=\mathrm{span}\{|T_f\rangle:|f|\le r\},\qquad \mathcal H_r=\mathcal H_{\le r}\ominus\mathcal H_{\le r-1},\qquad \mathcal H_{\le-1}=0,
--   $$
--   with orthogonal projectors $\Pi_{\le r}$ and $\Pi_r$. On the database side, $\mathcal L_r=\mathcal H(\mathcal I_r)$, with orthogonal projector $L_r$.
--
--   The synthesis operator is $E_r|f\rangle=|T_f\rangle$. Further
--   $$
--   \Gamma_r=\Pi_rE_r,\quad G_r=\Gamma_r\Gamma_r^\dagger,\quad K_r=\mathrm{ran}(\Gamma_r^\dagger),\quad V_r=\Gamma_r^\dagger G_r^{-1},\quad \tilde V_r=\Gamma_r^\dagger G_r^{-1/2},
--   $$
--   and $V=\bigoplus_{r=0}^{N-1}V_r$, $\tilde V=\bigoplus_{r=0}^{N-1}\tilde V_r$. The map $\tilde V$ is the compression isometry, and $V$ the related contraction.
--
--   **Formalization Note** $G_r$ vanishes off $\mathcal H_r$ and is invertible on $\mathcal H_r$, so $G_r^{-1}$ and $G_r^{-1/2}$ are the inverses on $\mathcal H_r$ extended by $0$. They are the functional calculus of $x\mapsto x^{-1}$ and $x\mapsto (\sqrt x)^{-1}$, with Lean's real convention $0^{-1}=0$. A plain matrix inverse would give $0$ here. $E_r$ is extended by $0$ from $\mathcal L_r$ to $\mathcal L$, and the direct sums are $\sum_{r<N}V_r\Pi_r$ and $\sum_{r<N}\tilde V_r\Pi_r$.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §4.1, pp.11–12: Definition 4.1, eqs. (7), (8), (9)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm

namespace CompPermOracle

variable {N : ℕ}

/-- `|T_f⟩ = ((N − r)!)^{-1/2} ∑_{φ ∈ T_f} |φ⟩`, the normalized completion state of `f ∈ ℐ_r`, with
`T_f = {φ ∈ S_N : φ|dom(f) = f}` (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03,
sha256 52ebc507…), §4.1, p.11). -/
noncomputable def completion (f : PartialPerm N) : Hil (Equiv.Perm (Fin N)) :=
  ((Real.sqrt ((N - size f).factorial : ℝ))⁻¹ : ℂ) •
    ∑ φ ∈ Finset.univ.filter (fun φ : Equiv.Perm (Fin N) => ∀ x y, f x = some y → φ x = y), ket φ

/-- `ℋ_{≤r} = span{|T_f⟩ : |f| ≤ r}` (arXiv:2609.28469, Definition 4.1, p.11). -/
noncomputable def Hle (N r : ℕ) : Submodule ℂ (Hil (Equiv.Perm (Fin N))) :=
  Submodule.span ℂ {v | ∃ f : PartialPerm N, size f ≤ r ∧ v = completion f}

/-- `ℋ_r = ℋ_{≤r} ⊖ ℋ_{≤r−1}`, with `ℋ_{≤−1} = 0` (arXiv:2609.28469, Definition 4.1, p.11). -/
noncomputable def Hlevel (N : ℕ) : ℕ → Submodule ℂ (Hil (Equiv.Perm (Fin N)))
  | 0 => Hle N 0
  | r + 1 => Hle N (r + 1) ⊓ (Hle N r)ᗮ

/-- `ℋ_{r−1}`, read as `0` at `r = 0` (arXiv:2609.28469, Lemma 4.5, p.13). -/
noncomputable def HlevelBelow (N : ℕ) : ℕ → Submodule ℂ (Hil (Equiv.Perm (Fin N)))
  | 0 => ⊥
  | r + 1 => Hlevel N r

/-- The orthogonal projector `Π_{≤r}` onto `ℋ_{≤r}` (arXiv:2609.28469, Definition 4.1, p.11). -/
noncomputable def ProjLe (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (Hle N r).starProjection

/-- The orthogonal projector `Π_r` onto `ℋ_r` (arXiv:2609.28469, Definition 4.1, p.11). -/
noncomputable def ProjLevel (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (Hlevel N r).starProjection

/-- `ℒ_r = ℋ(ℐ_r)`, as a subspace of `ℒ = ℋ(ℐ)` (arXiv:2609.28469, Definition 3.4, p.7). -/
noncomputable def Lsub (N r : ℕ) : Submodule ℂ (Hil (PartialPerm N)) :=
  Submodule.span ℂ {v | ∃ f : PartialPerm N, size f = r ∧ v = ket f}

/-- `ℒ_{r−1}`, read as `0` at `r = 0` (arXiv:2609.28469, Lemma 4.5, p.13). -/
noncomputable def LsubBelow (N : ℕ) : ℕ → Submodule ℂ (Hil (PartialPerm N))
  | 0 => ⊥
  | r + 1 => Lsub N r

/-- The orthogonal projector `L_j` from `ℒ` onto `ℒ_j` (arXiv:2609.28469, §4.2, p.13). -/
noncomputable def Lproj (N j : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f ∈ levelSet N j, ketBra (ket f) (ket f)

/-- The synthesis operator `E_r|f⟩ = |T_f⟩` for `f ∈ ℐ_r` (arXiv:2609.28469, Definition 4.1, eq. (7),
p.11).

**Formalization Note.** The source's `E_r` has domain `ℒ_r`. Here it is extended by `0` to `ℒ`. -/
noncomputable def synth (N r : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  ∑ f ∈ levelSet N r, ketBra (completion f) (ket f)

/-- `Γ_r = Π_r E_r` (arXiv:2609.28469, eq. (8), p.11). -/
noncomputable def Gam (N r : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (ProjLevel N r).comp (synth N r)

/-- The Gram operator `G_r = Γ_r Γ_r†` (arXiv:2609.28469, eq. (8), p.11). -/
noncomputable def Gram (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (Gam N r).comp (ContinuousLinearMap.adjoint (Gam N r))

/-- `K_r = ran(Γ_r†)` (arXiv:2609.28469, eq. (8), p.11). -/
noncomputable def Kr (N r : ℕ) : Submodule ℂ (Hil (PartialPerm N)) :=
  LinearMap.range (ContinuousLinearMap.adjoint (Gam N r)).toLinearMap

/-- The orthogonal projector `Π_{K_r}` onto `K_r` (arXiv:2609.28469, eq. (8), p.11). -/
noncomputable def ProjK (N r : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  (Kr N r).starProjection

/-- `G_r^{−1}`: the inverse of `G_r` on `ℋ_r`, extended by `0` (arXiv:2609.28469, eq. (9), p.12).

**Formalization Note.** `G_r` vanishes off `ℋ_r` and is invertible on `ℋ_r` (Lemma 4.9), so the
source's `G_r^{−1}` is the Moore–Penrose pseudo-inverse. It is the functional calculus of
`x ↦ x⁻¹`, where Lean's real `0⁻¹ = 0` is what extends it by `0`. -/
noncomputable def GramInv (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  cfc (fun x : ℝ => x⁻¹) (Gram N r)

/-- `G_r^{−1/2}`: the inverse square root of `G_r` on `ℋ_r`, extended by `0` (arXiv:2609.28469,
eq. (9), p.12). -/
noncomputable def GramInvSqrt (N r : ℕ) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Gram N r)

/-- `G_r^{1/2}` (arXiv:2609.28469, Lemma 4.10, eq. (38), p.18). -/
noncomputable def GramSqrt (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  cfc (fun x : ℝ => Real.sqrt x) (Gram N r)

/-- `V_r = Γ_r† G_r^{−1}` (arXiv:2609.28469, eq. (9), p.12). -/
noncomputable def Vr (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  (ContinuousLinearMap.adjoint (Gam N r)).comp (GramInv N r)

/-- `Ṽ_r = Γ_r† G_r^{−1/2}` (arXiv:2609.28469, eq. (9), p.12). -/
noncomputable def Vtr (N r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  (ContinuousLinearMap.adjoint (Gam N r)).comp (GramInvSqrt N r)

/-- The contraction `V = ⨁_{r=0}^{N−1} V_r` (arXiv:2609.28469, eq. (9), p.12).

**Formalization Note.** The direct sum over `𝒫 = ⨁_{r=0}^{N−1} ℋ_r` is `∑_r V_r Π_r`. -/
noncomputable def Vmap (N : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  ∑ r ∈ Finset.range N, (Vr N r).comp (ProjLevel N r)

/-- The compression isometry `Ṽ = ⨁_{r=0}^{N−1} Ṽ_r` (arXiv:2609.28469, eq. (9), p.12).

**Formalization Note.** The direct sum over `𝒫 = ⨁_{r=0}^{N−1} ℋ_r` is `∑_r Ṽ_r Π_r`. -/
noncomputable def Vtmap (N : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  ∑ r ∈ Finset.range N, (Vtr N r).comp (ProjLevel N r)

end CompPermOracle


