-- Prove2me | Definitions.Def_AC02Frege_approximants
-- name    : AC02Frege_approximants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:21.816412+00:00
-- url     : https://prove2.me/theorems/fbbca9bd-01ee-47a2-8fbc-2179f47c6798
-- title:
--   Two-level approximants $A_{\mathcal T}$, $P_L$ and the error families (39), (40)
-- statement:
--   Choose integers $t_{in},t_{out}\ge1$ and put $R=bt_{in}$. For each distinct term $\mathcal T$ and each line $L$ choose
--   $$
--   A_{\mathcal T}=\prod_{\nu=1}^{t_{in}}q_{\mathcal T,\nu},\quad q_{\mathcal T,\nu}=1+\sum_{j\in I_{\mathcal T}}a_{\mathcal T,\nu,j}(1+u_{\mathcal T,j}),\qquad P_L=\prod_{\nu=1}^{t_{out}}q_{L,\nu},\quad q_{L,\nu}=1+\sum_{\mathcal T\in L}a_{L,\nu,\mathcal T}A_{\mathcal T},
--   $$
--   with all coefficients in $\mathbb F_2$ and the same $A_{\mathcal T}$ at every occurrence of $\mathcal T$. A singleton uses the exact approximant $A_{(u=1)}=u$ and the empty term $A_\top=1$; then $P_\emptyset=1$.
--
--   For a common multiplier $f$, the two families of error conditions are
--   $$
--   fA_{\mathcal T}(1+u_{\mathcal T,j})\in\widehat C_D \text{ for every term and each of its equations},\tag{39}
--   $$
--   $$
--   fP_LA_{\mathcal T}\in\widehat C_D \text{ for every line and each of its terms}.\tag{40}
--   $$
--
--   **Formalization Note** The coefficients are functions of the term (resp. line), which forces the same approximant at every occurrence. Products are multilinearized.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 5.1, (39), (40), p.30

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_D35Refutation
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- The coefficients of the two-level approximants of Definition 5.1 (p.30) with `t_in` inner and
`t_out` outer factors: `a_{T,ν,j} ∈ 𝔽₂` for every term `T`, factor `ν` and equation `u_{T,j}` of
`T`, and `a_{L,ν,T} ∈ 𝔽₂` for every line `L`, factor `ν` and term `T` of `L`.

**Formalization Note** The coefficients are functions of the term (resp. line) itself, so the
same `A_T` is used at every occurrence of `T`, as Definition 5.1 requires. -/
structure Approx (V : Type*) [DecidableEq V] (tin tout : ℕ) where
  aT : Term V → Fin tin → MvPolynomial V (ZMod 2) → ZMod 2
  aL : Line V → Fin tout → Term V → ZMod 2

namespace Approx

variable {V : Type*} [DecidableEq V] {tin tout : ℕ}

/-- The **term approximant** (Definition 5.1, p.30): `A_⊤ = 1` for the empty term,
`A_{(u=1)} = u` for a singleton, and otherwise `A_T = ∏_{ν=1}^{t_in} q_{T,ν}` with
`q_{T,ν} = 1 + Σ_{j ∈ I_T} a_{T,ν,j} (1 + u_{T,j})`, multilinearized. -/
noncomputable def A (Φ : Approx V tin tout) (T : Term V) : MvPolynomial V (ZMod 2) :=
  open Classical in
  if T = ∅ then 1
  else if h : ∃ u, T = {u} then h.choose
  else ML (∏ ν : Fin tin, (1 + ∑ u ∈ T, Φ.aT T ν u • (1 + u)))

/-- The **line approximant** (Definition 5.1, p.30): `P_L = ∏_{ν=1}^{t_out} q_{L,ν}` with
`q_{L,ν} = 1 + Σ_{T ∈ L} a_{L,ν,T} A_T`, multilinearized. For the empty line `P_∅ = 1`. -/
noncomputable def P (Φ : Approx V tin tout) (L : Line V) : MvPolynomial V (ZMod 2) :=
  ML (∏ ν : Fin tout, (1 + ∑ T ∈ L, Φ.aL L ν T • Φ.A T))

end Approx

/-- The **inner error conditions** (39) (Definition 5.1, p.30): `f A_T (1 + u_{T,j}) ∈ Ĉ_D` for
every term `T` occurring in the refutation `π` and each of its equations `u_{T,j} = 1`. -/
def InnerErr {n : ℕ} (F : CNF (Fin n)) (ℓ D : ℕ) {tin tout : ℕ}
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ)))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : Prop :=
  ∀ L ∈ π, ∀ T ∈ L, ∀ u ∈ T, f * Φ.A T * (1 + u) ∈ CHat F ℓ D

/-- The **outer error conditions** (40) (Definition 5.1, p.30): `f P_L A_T ∈ Ĉ_D` for every line
`L` of the refutation `π` and each of its terms `T`. -/
def OuterErr {n : ℕ} (F : CNF (Fin n)) (ℓ D : ℕ) {tin tout : ℕ}
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ)))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : Prop :=
  ∀ L ∈ π, ∀ T ∈ L, f * Φ.P L * Φ.A T ∈ CHat F ℓ D

end AC02Frege


