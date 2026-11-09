-- Prove2me | Definitions.Def_WeldedPath_piIntertwiner
-- name    : WeldedPath_piIntertwiner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:14:04.755245+00:00
-- url     : https://prove2.me/theorems/9479523b-96f9-4165-855c-e03c372bc3c6
-- title:
--   Product intertwiners $\mathcal I_P$ and operators on one permutation register
-- statement:
--   For a family of permutation registers $\mathrm P_k$ of sizes $s_k$, the product intertwiner
--   $$
--   \mathcal I_{\mathrm P}=\bigotimes_k\mathcal I_{s_k}
--   $$
--   maps the joint permutation register to the joint database register; its matrix entries are $\langle I|\mathcal I_{\mathrm P}|\phi\rangle=\prod_k\langle I_k|\mathcal I_{s_k}|\phi_k\rangle$. An operator $T$ on one register $\mathrm P_k$ acts on the joint register as $(T)_{\mathrm P_k}$, the identity on the others. $\Pi_{s,\le r}$ is the projector onto $\mathcal H_{s,\le r}$.
--
--   In the welded trees analysis $\mathcal I_{\mathrm P}=\mathcal I_M\otimes\bigotimes_{b\in B_{\mathrm{edge}}}\mathcal I_{|E_b|}$ (41) compresses the label permutation and every edge permutation at once.
--
--   **Formalization Note** The joint registers are dependent function types over the finite index set of registers.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), (41), p.20; Lemma 3.11, p.24

import Mathlib
import Definitions.Def_WeldedPath_exactCpO

namespace WeldedPath

open InjDb

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The product `I_P = ⨂_k I_{s_k}` of the intertwiners (12) of a family of permutation registers
`P_k` of sizes `s_k`, from `⨂_k H(Sym(s_k))` to `⨂_k H(I_{s_k})` (Carolan, Childs, Coudron, Gilani,
Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…), (41), p.20, and Lemma 3.11, p.24).

**Formalization Note.** The joint registers are the function types `(k : K) → Sym(s_k)` and
`(k : K) → I_{s_k}`; the tensor product is given by its matrix entries
`⟨I|I_P|ϕ⟩ = Π_k ⟨I_k|I_{s_k}|ϕ_k⟩`. -/
noncomputable def piIntertwiner (sz : K → ℕ) :
    Hil ((k : K) → Equiv.Perm (Fin (sz k))) →L[ℂ] Hil ((k : K) → InjDb (sz k)) :=
  ∑ ϕ : (k : K) → Equiv.Perm (Fin (sz k)), ∑ I : (k : K) → InjDb (sz k),
    (∏ k, inner ℂ (ket (I k)) (intertwiner (sz k) (ket (ϕ k)))) • ketBra (ket I) (ket ϕ)

/-- An operator `T` on the permutation register `P_k`, tensored with the identity on the other
registers `P_{k'}`, `k' ≠ k`; written `(T)_{P_k}` (arXiv:2611.05912 (sha256 b31400a0…), p.24). -/
noncomputable def onFactor (sz : K → ℕ) (k : K)
    (T : Hil (Equiv.Perm (Fin (sz k))) →L[ℂ] Hil (Equiv.Perm (Fin (sz k)))) :
    Hil ((k : K) → Equiv.Perm (Fin (sz k))) →L[ℂ] Hil ((k : K) → Equiv.Perm (Fin (sz k))) :=
  ∑ ϕ : (k : K) → Equiv.Perm (Fin (sz k)), ∑ ϕ' : (k : K) → Equiv.Perm (Fin (sz k)),
    (if ∀ k', k' ≠ k → ϕ' k' = ϕ k' then inner ℂ (ket (ϕ' k)) (T (ket (ϕ k))) else 0) •
      ketBra (ket ϕ') (ket ϕ)

/-- The projector `Π_{s,≤r}` onto `H_{s,≤r}` (arXiv:2611.05912 (sha256 b31400a0…), p.12). -/
noncomputable def projLe (s r : ℕ) : Hil (Equiv.Perm (Fin s)) →L[ℂ] Hil (Equiv.Perm (Fin s)) :=
  (Hle s r).starProjection

end WeldedPath


