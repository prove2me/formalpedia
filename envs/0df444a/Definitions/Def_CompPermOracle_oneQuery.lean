-- Prove2me | Definitions.Def_CompPermOracle_oneQuery
-- name    : CompPermOracle_oneQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:29.044321+00:00
-- url     : https://prove2.me/theorems/af2a0b5c-c193-49cd-8671-c9d31c9a7ef5
-- title:
--   One-query maps: $z^+$, $z^0$, $h^0$, $h^-$, selectors $R^{00}$, $R^{11}$, operators $A$, $H^{00}$, $H^{11}$, and the one-query error
-- statement:
--   Fix $x\in[N]$ and write $Q_y=Q_{x,y}$, $M_y=M_{x,y}$, $m=N-r$. With $b^+_{y,r}=L_{r+1}M_yV_r$, $b^0_{y,r}=L_rM_yV_r$ and $b^-_{y,r}=L_{r-1}M_yV_r$, put
--   $$
--   z^+_{y,r}=(I-\Pi_{K_{r+1}})b^+_{y,r},\quad z^0_{y,r}=(I-\Pi_{K_r})b^0_{y,r},
--   $$
--   $$
--   h^0_{y,r}\psi=\Pi_{K_r}b^0_{y,r}\psi-V_r\Pi_rQ_y\psi,\quad h^-_{y,r}\psi=b^-_{y,r}\psi-V_{r-1}\Pi_{r-1}Q_y\psi\qquad(\psi\in\mathcal H_r).
--   $$
--   For $r=0$, every object carrying the superscript $-$ or the subscript $r-1$ is zero.
--
--   On $\mathcal L_r$, the diagonal selectors are $R^{00}_{x,y;r}=\sum_{f\in\mathcal I_r,\,x\notin\mathrm{dom}(f),\,y\notin\mathrm{im}(f)}|f\rangle\langle f|$ and $R^{11}_{x,y;r}=\sum_{f\in\mathcal I_r,\,f(x)=y}|f\rangle\langle f|$. Further, $A_{y,r}=\Pi_rQ_y\Pi_r$, $H^{00}_{y,r}=\frac1m\Gamma_rR^{00}_{x,y;r}\Gamma_r^\dagger$ and $H^{11}_{y,r}=\Gamma_rR^{11}_{x,y;r}\Gamma_r^\dagger$.
--
--   The one-query error of a map $W:\mathcal P\to\mathcal L$ is $(\mathrm{cpO}_x(I_{\mathcal A}\otimes W)-(I_{\mathcal A}\otimes W)P_x)(I_{\mathcal A}\otimes\Pi_{\le t})$, and similarly for inverse and for coherently controlled queries.
--
--   **Formalization Note** $h^0_{y,r}$ and $h^-_{y,r}$ are operators on $\mathcal P$ precomposed with $\Pi_r$. The family $z^+\oplus z^0$ of the source is the sum `zPlus + zZero` in $\mathcal L$: the two maps land in the orthogonal subspaces $\mathcal L_{r+1}$ and $\mathcal L_r$, so $\mathrm{Col}$ and $\mathrm{Row}$ agree with those of the direct sum.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eqs. (18)–(22), p.14; eqs. (67), (68), p.23; eqs. (11), (12), p.12

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels

namespace CompPermOracle

variable {N : ℕ}

/-- `z⁺_{y,r} = (I − Π_{K_{r+1}}) b⁺_{y,r}`, with `b⁺_{y,r} = L_{r+1} M_y V_r` (Carolan, Majenz,
arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eqs. (18) and (20), p.14). -/
noncomputable def zPlus (x y : Fin N) (r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  (1 - ProjK N (r + 1)).comp ((Lproj N (r + 1)).comp ((compM x y).comp (Vr N r)))

/-- `z⁰_{y,r} = (I − Π_{K_r}) b⁰_{y,r}`, with `b⁰_{y,r} = L_r M_y V_r` (arXiv:2609.28469, eqs. (18)
and (20), p.14). -/
noncomputable def zZero (x y : Fin N) (r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  (1 - ProjK N r).comp ((Lproj N r).comp ((compM x y).comp (Vr N r)))

/-- The family `z⁺_{y,r} ⊕ z⁰_{y,r}` of eq. (23) (arXiv:2609.28469, p.14).

**Formalization Note.** The source maps into `ℒ_{r+1} ⊕ ℒ_r`. These are orthogonal subspaces of `ℒ`,
so the sum in `ℒ` differs from the direct sum by an isometric embedding, and `Col` and `Row` agree. -/
noncomputable def zSum (x y : Fin N) (r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  zPlus x y r + zZero x y r

/-- `h⁰_{y,r} ψ = Π_{K_r} b⁰_y − V_r Π_r Q_y ψ` for `ψ ∈ ℋ_r` (arXiv:2609.28469, eq. (21), p.14).

**Formalization Note.** The source defines it on `ℋ_r`. As an operator on `𝒫` it is precomposed
with `Π_r`. -/
noncomputable def hZero (x y : Fin N) (r : ℕ) : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N) :=
  ((ProjK N r).comp ((Lproj N r).comp ((compM x y).comp (Vr N r)))).comp (ProjLevel N r) -
    (Vr N r).comp ((ProjLevel N r).comp ((assertP x y).comp (ProjLevel N r)))

/-- `h⁻_{y,r} ψ = b⁻_y − V_{r−1} Π_{r−1} Q_y ψ` for `ψ ∈ ℋ_r`, with `b⁻_{y,r} = L_{r−1} M_y V_r`, and
`h⁻_{y,0} = 0` (arXiv:2609.28469, eqs. (19) and (22), p.14: "For r = 0, every object carrying the
superscript − or the subscript r − 1 is omitted and understood to be zero").

**Formalization Note.** As an operator on `𝒫` it is precomposed with `Π_r`. -/
noncomputable def hMinus (x y : Fin N) : ℕ → (Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N))
  | 0 => 0
  | r + 1 =>
    ((Lproj N r).comp ((compM x y).comp (Vr N (r + 1)))).comp (ProjLevel N (r + 1)) -
      (Vr N r).comp ((ProjLevel N r).comp ((assertP x y).comp (ProjLevel N (r + 1))))

/-- The diagonal selector `R⁰⁰_{x,y;r} = ∑_{f ∈ ℐ_r, x ∉ dom(f), y ∉ im(f)} |f⟩⟨f|`
(arXiv:2609.28469, eq. (67), p.23). -/
noncomputable def selR00 (x y : Fin N) (r : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f ∈ (levelSet N r).filter (fun f => NotInDom f x ∧ NotInIm f y), ketBra (ket f) (ket f)

/-- The diagonal selector `R¹¹_{x,y;r} = ∑_{f ∈ ℐ_r, f(x)=y} |f⟩⟨f|` (arXiv:2609.28469, eq. (67),
p.23). -/
noncomputable def selR11 (x y : Fin N) (r : ℕ) : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f ∈ (levelSet N r).filter (fun f => f x = some y), ketBra (ket f) (ket f)

/-- `A_{y,r} = Π_r Q_y Π_r` (arXiv:2609.28469, eq. (68), p.23). -/
noncomputable def opA (x y : Fin N) (r : ℕ) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (ProjLevel N r).comp ((assertP x y).comp (ProjLevel N r))

/-- `H⁰⁰_{y,r} = (1/m) Γ_r R⁰⁰_{x,y;r} Γ_r†`, with `m = N − r` (arXiv:2609.28469, eq. (68), p.23). -/
noncomputable def opH00 (x y : Fin N) (r : ℕ) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (((((N : ℝ) - r)⁻¹ : ℝ) : ℂ)) •
    (Gam N r).comp ((selR00 x y r).comp (ContinuousLinearMap.adjoint (Gam N r)))

/-- `H¹¹_{y,r} = Γ_r R¹¹_{x,y;r} Γ_r†` (arXiv:2609.28469, eq. (68), p.23). -/
noncomputable def opH11 (x y : Fin N) (r : ℕ) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  (Gam N r).comp ((selR11 x y r).comp (ContinuousLinearMap.adjoint (Gam N r)))

/-- The one-query error `(cpO(I_𝒜 ⊗ W) − (I_𝒜 ⊗ W)P)(I_𝒜 ⊗ Π_{≤t})` of the map `W : 𝒫 → ℒ`, for a
query point and direction given by the operators `O` on `𝒜 ⊗ ℒ` and `P` on `𝒜 ⊗ 𝒫`
(arXiv:2609.28469, eqs. (11) and (12), p.12). -/
noncomputable def queryErr (Wm : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N))
    (O : Hil (Ans N × PartialPerm N) →L[ℂ] Hil (Ans N × PartialPerm N))
    (P : Hil (Ans N × Equiv.Perm (Fin N)) →L[ℂ] Hil (Ans N × Equiv.Perm (Fin N))) (t : ℕ) :
    Hil (Ans N × Equiv.Perm (Fin N)) →L[ℂ] Hil (Ans N × PartialPerm N) :=
  (O.comp (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) Wm) -
      (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) Wm).comp P).comp
    (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) (ProjLe N t))

/-- The same one-query error for operators coherently controlled on the query point `[N]`
(arXiv:2609.28469, Theorem 4.2, last sentence, p.12). -/
noncomputable def queryErrCtl (Wm : Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (PartialPerm N))
    (O : Hil (Fin N × (Ans N × PartialPerm N)) →L[ℂ] Hil (Fin N × (Ans N × PartialPerm N)))
    (P : Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) →L[ℂ] Hil (Fin N × (Ans N × Equiv.Perm (Fin N))))
    (t : ℕ) :
    Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) →L[ℂ] Hil (Fin N × (Ans N × PartialPerm N)) :=
  (O.comp (opTensor (1 : Hil (Fin N) →L[ℂ] Hil (Fin N))
        (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) Wm)) -
      (opTensor (1 : Hil (Fin N) →L[ℂ] Hil (Fin N))
        (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) Wm)).comp P).comp
    (opTensor (1 : Hil (Fin N) →L[ℂ] Hil (Fin N))
      (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) (ProjLe N t)))

end CompPermOracle


