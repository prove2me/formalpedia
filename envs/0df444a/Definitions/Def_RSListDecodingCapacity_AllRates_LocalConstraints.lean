-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_LocalConstraints
-- name    : RSListDecodingCapacity_AllRates_LocalConstraints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:56.602016+00:00
-- url     : https://prove2.me/theorems/ba536394-ac6d-4cc6-95c5-ac1173322550
-- title:
--   The local substitution (15) and the local constraints (16) at a received point
-- statement:
--   Fix a received point $(\alpha,y)\in\mathbb F^2$. For $Q\in\mathbb F[X,Y_0,\dots,Y_d]$ the **local substitution** is
--   $$Q_{(\alpha,y)}(T,E,Y_1,\dots,Y_d)=Q\Big(\alpha+T,\ y+\sum_{j=1}^d(-1)^{j+1}T^jY_j+TE,\ Y_1,\dots,Y_d\Big)=\sum_{b,\vec e}q_{b,\vec e}(T)\,E^bY_1^{e_1}\cdots Y_d^{e_d}.$$
--   $Q$ **satisfies the local constraints (16)** at $(\alpha,y)$ if for every $(b,\vec e)\in\mathbb Z_{\ge0}^{d+1}$ with $db<m$,
--   $$q_{b,\vec e}(T)\equiv0\pmod{T^{m-db}},$$
--   that is, the coefficient of $T^iE^bY^{\vec e}$ in $Q_{(\alpha,y)}$ vanishes whenever $db<m$ and $i<m-db$. These are homogeneous linear conditions on the coefficients of $Q$.
--
--   They are designed so that every polynomial $P$ with $P(\alpha)=y$ makes $Q(X,P,P^{[1]},\dots,P^{[d]})$ vanish to order $m$ at $\alpha$ (Lemma 3.1).
--
--   **Formalization Note** The variables $T,E,Y_1,\dots,Y_d$ form the type `LVar d`, with `Y j` the source's $Y_{j+1}$.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §3, Local Constraints at Each Received Point, p.14, (15)–(16)

import Mathlib

namespace RSListDecodingCapacity.AllRates

/-- The variables `T, E, Y₁, …, Y_d` of the local substitution (15) (p.14); `Y j` (`j : Fin d`) is
the source's `Y_{j+1}`. -/
inductive LVar (d : ℕ) where
  | T : LVar d
  | E : LVar d
  | Y : Fin d → LVar d

/-- **The local substitution (15)** at a received point `(α, y)` (p.14):
`Q ↦ Q(α + T, y + ∑_{j=1}^{d} (−1)^{j+1} T^j Y_j + T E, Y₁, …, Y_d) ∈ 𝔽[T, E, Y₁, …, Y_d]`.
Here `Q ∈ 𝔽[X, Y₀, …, Y_d]`, with variables `none = X` and `some j = Y_j`; the Lean index
`i : Fin d` of the sum stands for `j = i + 1`, so `(−1)^{j+1} T^j = (−1)^{i+2} T^{i+1}`. -/
noncomputable def localSubst {F : Type*} [CommRing F] (d : ℕ) (α y : F) :
    MvPolynomial (Option (Fin (d + 1))) F →ₐ[F] MvPolynomial (LVar d) F :=
  MvPolynomial.aeval fun v => Option.elim v (MvPolynomial.C α + MvPolynomial.X LVar.T) fun j =>
    Fin.cases (motive := fun _ => MvPolynomial (LVar d) F)
      (MvPolynomial.C y + ∑ i : Fin d, (-1 : MvPolynomial (LVar d) F) ^ ((i : ℕ) + 2) *
          MvPolynomial.X LVar.T ^ ((i : ℕ) + 1) * MvPolynomial.X (LVar.Y i) + MvPolynomial.X LVar.T * MvPolynomial.X LVar.E)
      (fun i => MvPolynomial.X (LVar.Y i)) j

/-- **The local constraints (16)** at `(α, y)` (p.14). Write
`Q_{(α,y)} = ∑_{b, e} q_{b,e}(T) E^b Y₁^{e₁} ⋯ Y_d^{e_d}`. For every `(b, e)` with `d b < m`,
`q_{b,e}(T) ≡ 0 mod T^{m − d b}`; that is, the coefficient of `T^i E^b Y^e` vanishes whenever
`d b < m` and `i < m − d b`. -/
def SatisfiesLocal {F : Type*} [CommRing F] (d m : ℕ) (α y : F)
    (Q : MvPolynomial (Option (Fin (d + 1))) F) : Prop :=
  ∀ s : LVar d →₀ ℕ, d * s LVar.E < m → s LVar.T < m - d * s LVar.E →
    MvPolynomial.coeff s (localSubst d α y Q) = 0

end RSListDecodingCapacity.AllRates


