-- Prove2me | Definitions.Def_CompPermOracle_incidence
-- name    : CompPermOracle_incidence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:55:01.040076+00:00
-- url     : https://prove2.me/theorems/3e5ffa74-3dca-4ac3-ac78-6b4ada5ac9e0
-- title:
--   Incidence maps $B^{\mathrm{im}}_j$, $B^{\mathrm{dom}}_j$ and the stack $\Theta_{y,r}$
-- statement:
--   For $1\le j\le N$ the **incidence maps** on $\mathcal L_j$ are
--   $$
--   (B^{\mathrm{im}}_ja)_{h,b}=\frac{1}{\sqrt{N-j+1}}\sum_{u\notin\mathrm{dom}(h)}a_{h[u\mapsto b]},\qquad (B^{\mathrm{dom}}_ja)_{h,u}=\frac{1}{\sqrt{N-j+1}}\sum_{b\notin\mathrm{im}(h)}a_{h[u\mapsto b]},
--   $$
--   for $h\in\mathcal I_{j-1}$, $b\notin\mathrm{im}(h)$ and $u\notin\mathrm{dom}(h)$ respectively, and $B^{\mathrm{dom}}_0=B^{\mathrm{im}}_0=0$. They measure failure of the zero-sum relations that define $K_j$.
--
--   In the convention of §4.4 from p.20 on, for $a\in K_r$ write $b^+_y=L_{r+1}M_ya$ and $b^0_y=L_rM_ya$, with no $V_r$. The stack of Lemma 4.13 is
--   $$
--   \Theta_{y,r}a=(B^{\mathrm{im}}_{r+1}b^+_y,\,B^{\mathrm{dom}}_{r+1}b^+_y,\,B^{\mathrm{im}}_rb^0_y,\,B^{\mathrm{dom}}_rb^0_y).
--   $$
--
--   **Formalization Note** The target is $\mathcal H(\mathcal I\times[N])$, of which the source's target is the coordinate subspace. The stack maps into $\mathcal H(\mathrm{Fin}\ 4\times\mathcal I\times[N])$ and is precomposed with $\Pi_{K_r}$, which expresses "as operators on $K_r$": $\mathrm{Col}$ and $\mathrm{Row}$ do not change.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eqs. (42), (43), p.19; Lemma 4.13, p.20

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels

namespace CompPermOracle

variable {N : ℕ}

/-- The incidence map `B^im_j`: `(B^im_j a)_{h,b} = (N − j + 1)^{-1/2} ∑_{u ∉ dom(h)} a_{h[u ↦ b]}` for
`h ∈ ℐ_{j−1}`, `b ∉ im(h)`, and `B^im_0 = 0` (Carolan, Majenz, arXiv:2609.28469 (version of
2026-11-03, sha256 52ebc507…), eq. (42), p.19).

**Formalization Note.** The source's target `⨁_{h ∈ ℐ_{j−1}, b ∉ im(h)} ℂ|h, b⟩` is the subspace of
`ℋ(ℐ × [N])` spanned by those basis vectors. The map is defined on all of `ℒ` through its matrix
entries, so it only reads the coefficients on `ℐ_j`. -/
noncomputable def Bim (N : ℕ) : ℕ → (Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N × Fin N))
  | 0 => 0
  | j + 1 =>
    ∑ h ∈ levelSet N j, ∑ b ∈ freeIm h, ∑ u ∈ freeDom h,
      (((Real.sqrt ((N : ℝ) - ((j + 1 : ℕ) : ℝ) + 1))⁻¹ : ℝ) : ℂ) •
        ketBra (ket (h, b)) (ket (addPair h u b))

/-- The incidence map `B^dom_j`: `(B^dom_j a)_{h,u} = (N − j + 1)^{-1/2} ∑_{b ∉ im(h)} a_{h[u ↦ b]}` for
`h ∈ ℐ_{j−1}`, `u ∉ dom(h)`, and `B^dom_0 = 0` (arXiv:2609.28469, eq. (43), p.19).

**Formalization Note.** As for `Bim`, the target is a subspace of `ℋ(ℐ × [N])`. -/
noncomputable def Bdom (N : ℕ) : ℕ → (Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N × Fin N))
  | 0 => 0
  | j + 1 =>
    ∑ h ∈ levelSet N j, ∑ u ∈ freeDom h, ∑ b ∈ freeIm h,
      (((Real.sqrt ((N : ℝ) - ((j + 1 : ℕ) : ℝ) + 1))⁻¹ : ℝ) : ℂ) •
        ketBra (ket (h, u)) (ket (addPair h u b))

/-- The inclusion of component `i` of a 4-fold direct sum. -/
noncomputable def injFour {X : Type} [Fintype X] [DecidableEq X] (i : Fin 4) :
    Hil X →L[ℂ] Hil (Fin 4 × X) :=
  ∑ p : X, ketBra (ket (i, p)) (ket p)

/-- The stack `Θ_{y,r} a = (B^im_{r+1} b⁺_y, B^dom_{r+1} b⁺_y, B^im_r b⁰_y, B^dom_r b⁰_y)` of Lemma 4.13
(arXiv:2609.28469, p.20), in the convention of §4.4 from p.20 on: `b⁺_y = L_{r+1} M_y a` and
`b⁰_y = L_r M_y a`, with no `V_r`.

**Formalization Note.** "As operators on `K_r`" is expressed by precomposing with `Π_{K_r}`. A family
`T_y` on `K_r` and its extension by `0` have the same `Col` and `Row`. -/
noncomputable def Theta (x y : Fin N) (r : ℕ) :
    Hil (PartialPerm N) →L[ℂ] Hil (Fin 4 × (PartialPerm N × Fin N)) :=
  ((injFour 0).comp ((Bim N (r + 1)).comp ((Lproj N (r + 1)).comp (compM x y))) +
    (injFour 1).comp ((Bdom N (r + 1)).comp ((Lproj N (r + 1)).comp (compM x y))) +
    (injFour 2).comp ((Bim N r).comp ((Lproj N r).comp (compM x y))) +
    (injFour 3).comp ((Bdom N r).comp ((Lproj N r).comp (compM x y)))).comp (ProjK N r)

end CompPermOracle


