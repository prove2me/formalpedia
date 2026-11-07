-- Prove2me | Definitions.Def_BoolCSPDel_fB
-- name    : BoolCSPDel_fB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:24.965407+00:00
-- url     : https://prove2.me/theorems/f627157d-6801-4600-8f8b-2cc91ebae96e
-- title:
--   The INDEX reduction: $\alpha_j$, $\beta_{j,t}$, $c_{j,t}$, $f_B(X,j)$, pinning
-- statement:
--   Fix a relation $R\in\Gamma$ of arity $a$, a tuple $b$ and a polynomial $q$. On the variables $x_{i,u}$, $i\in[a]$, $u\in[n]$, the assignment $\alpha_j$ gives $x_{i,u}$ the value $b_i$ if $u=j_i$ and $1-b_i$ otherwise (4.6). With $C_t=R(x_{1,t_1},\dots,x_{a,t_a})$, put $\beta_{j,t}=q(C_t(\alpha_j))$ (4.7) and
--
--   $$c_{j,t}(X)=\beta_{j,t}X_t+(-\beta_{j,t})_+,\qquad f_B(X,j)=P+\sum_t c_{j,t}(X)\,e_{C_t}$$
--
--   (4.11), for a pinning instance $P$ on the variables and additional ones. $P$ **pins** $\alpha$ if the assignments extending to its solutions are exactly $\{g\circ\alpha:g\in\mathrm{Aut}(\Gamma)\}$. Finally $F_R=\max\{1,\max_x|q(x)|\}$.
--
--   This is the hard instance family of the lower bound: unsatisfiable exactly when $X_j=1$.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), (4.6), p.25; (4.7), p.26; (4.11), p.27; p.19

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_IsCore
import Definitions.Def_BoolCSPDel_Con

namespace BoolCSPDel

/-- **The INDEX reduction.** Bandekar, Sharma, Velusamy, STOC 2027 submission (manuscript sha256
15f83519…), (4.6), p.25: `α_j(x_{a,u}) = b_a` if `u = j_a`, and `1 − b_a` otherwise. The variables are
`x_{a,u} = (a, u) ∈ Fin a₀ × Fin n`. -/
def alphaJ {a n : ℕ} (b : Fin a → Bool) (j : Fin a → Fin n) : Fin a × Fin n → Bool :=
  fun v => if v.2 = j v.1 then b v.1 else !b v.1

/-- (4.7), p.26: `β_{j,t} = q(C_t(α_j))`, where `C_t(α)` is the tuple assigned to the scope of `C_t`. -/
noncomputable def betaJT {a n : ℕ} (q : MvPolynomial (Fin a) ℤ) (b : Fin a → Bool)
    (j t : Fin a → Fin n) : ℤ :=
  evalAt q fun i => alphaJ b j (i, t i)

/-- (4.11), p.27: `c_{j,t}(X) = β_{j,t} X_t + (−β_{j,t})_+`. -/
noncomputable def cJT {a n : ℕ} (q : MvPolynomial (Fin a) ℤ) (b : Fin a → Bool)
    (X : (Fin a → Fin n) → Bool) (j t : Fin a → Fin n) : ℤ :=
  betaJT q b j t * (if X t then 1 else 0) + max (-betaJT q b j t) 0

/-- p.25: the constraint `C_t = R(x_{1,t_1}, …, x_{a,t_a})`, on the variables `V` of the reduction
inside `V ∪ Y`. -/
def dataCon {k : ℕ} {Γ : Lang k} (R : Rel k) (hR : R ∈ Γ) {n Y : ℕ} (t : Fin R.1 → Fin n) :
    Con Γ ((Fin R.1 × Fin n) ⊕ Fin Y) :=
  ⟨⟨R, hR⟩, fun i => Sum.inl (i, t i)⟩

/-- (4.11), p.27: `f_B = P_{α_j} + Σ_t c_{j,t}(X) e_{C_t}`, for a pinning instance `P` on `V ∪ Y`
(each of its constraints once). -/
noncomputable def fB {k : ℕ} {Γ : Lang k} (R : Rel k) (hR : R ∈ Γ) {n Y : ℕ}
    (P : Finset (Con Γ ((Fin R.1 × Fin n) ⊕ Fin Y))) (q : MvPolynomial (Fin R.1) ℤ)
    (b : Fin R.1 → Bool) (X : (Fin R.1 → Fin n) → Bool) (j : Fin R.1 → Fin n)
    (C : Con Γ ((Fin R.1 × Fin n) ⊕ Fin Y)) : ℤ :=
  (if C ∈ P then 1 else 0) + ∑ t, if C = dataCon R hR t then cJT q b X j t else 0

/-- p.19: `P` pins `α` up to a common automorphism of `Γ`: the assignments on `V` extending to a
solution of `P` are exactly `{g ∘ α : g ∈ Aut(Γ)}`. -/
def IsPinning {k : ℕ} {Γ : Lang k} {V : Type} {Y : ℕ} (P : Finset (Con Γ (V ⊕ Fin Y)))
    (α : V → Bool) : Prop :=
  {β | ∃ γ ∈ SatSet P, β = γ ∘ Sum.inl} = {β | ∃ g, IsAutLang Γ g ∧ β = g ∘ α}

/-- p.27: `F_R = max{1, max_a |q(a)|}`. -/
noncomputable def freqBound {a : ℕ} (q : MvPolynomial (Fin a) ℤ) : ℕ :=
  max 1 (Finset.univ.sup fun x : Fin a → Bool => (evalAt q x).natAbs)

end BoolCSPDel


