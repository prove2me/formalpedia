-- Prove2me | Definitions.Def_LinSSWorst_additiveMap
-- name    : LinSSWorst_additiveMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:56.819107+00:00
-- url     : https://prove2.me/theorems/af058d58-b38b-4502-9381-e23eba116d24
-- title:
--   Additive secret sharing (Definition A.5)
-- statement:
--   Let $F$ be a finite field, $q\ge 1$, and let $P_1,\dots,P_q$ be parties. To share $a\in F$ **additively**, the dealer takes random elements $r_1,\dots,r_{q-1}\in F$, gives $r_j$ to $P_j$ for every $j<q$, and gives
--   $$a-\sum_{j=1}^{q-1} r_j$$
--   to $P_q$. As a map of the secret and the randomness, $(a,r)\mapsto(r_1,\dots,r_{q-1},a-\sum_j r_j)$ is $F$-linear, so it is a linear secret-sharing scheme in which every party holds one field element.
--
--   Additive sharing is the building block of the masking side of the main construction.
--
--   **Formalization Note** With $q=m+1$ the parties are `Fin (m + 1)`, the randomness is `Fin m → F`, and the last party is `Fin.last m`. Each share is a vector of length one (`Fin 1 → F`).
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition A.5, p.30

import Mathlib

namespace LinSSWorst

/-- **Additive secret sharing** (Definition A.5, p.30), from O. Nir, *Resolving the Worst-Case
Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02,
sha256 5521cfdb…). To share `a ∈ F` among `q = m + 1` parties `P_1, …, P_q`, the dealer uses
random elements `r_1, …, r_{q-1}`, gives `r_j` to `P_j` for `j < q`, and gives
`a − Σ_{j=1}^{q-1} r_j` to `P_q`.

**Formalization Note.** The parties are `Fin (m + 1)`, the random elements `r : Fin m → F`, and
the last party `P_q` is `Fin.last m` (the index `m`). Writing `q = m + 1` covers every `q ≥ 1`. -/
def additiveShares {F : Type*} [Field F] (m : ℕ) (a : F) (r : Fin m → F) : Fin (m + 1) → F :=
  fun j => if h : (j : ℕ) < m then r ⟨j, h⟩ else a - ∑ k, r k

/-- Additive secret sharing (Definition A.5, p.30) as a linear secret-sharing scheme in the sense
of Definition A.3: the `F`-linear map `(a, r) ↦ (additiveShares m a r j)_j` from `F^{1+m}` to
`F^{1+⋯+1}`, every one of the `m + 1` parties holding one field element.

**Formalization Note.** Each share is a vector indexed by `Fin 1` (share length `ℓ_j = 1`). -/
def additiveMap (F : Type*) [Field F] (m : ℕ) :
    (F × (Fin m → F)) →ₗ[F] ((j : Fin (m + 1)) → Fin 1 → F) where
  toFun p := fun j _ => additiveShares m p.1 p.2 j
  map_add' p p' := by
    funext j t
    simp only [additiveShares, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' c p := by
    funext j t
    simp only [additiveShares, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, ← Finset.mul_sum]
    split_ifs <;> ring

end LinSSWorst


