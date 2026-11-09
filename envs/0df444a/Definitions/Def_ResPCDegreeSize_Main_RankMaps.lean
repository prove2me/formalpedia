-- Prove2me | Definitions.Def_ResPCDegreeSize_Main_RankMaps
-- name    : ResPCDegreeSize_Main_RankMaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:15.240573+00:00
-- url     : https://prove2.me/theorems/1534c907-4310-4461-a5e6-d4d1a99b5d99
-- title:
--   Multiplication maps modulo $\mathcal C_D$, the field $\mathbb F_p(\lambda)$, Razborov–Smolensky products and truth indicators
-- statement:
--   This module collects the linear-algebraic objects of Sections 2–5.
--
--   For a field extension $E/\mathbb F_p$ and a subspace $W\subseteq\mathbb F_p[x]$, $E\otimes_{\mathbb F_p}W$ is regarded as the $E$-span of $W$ inside $E[x]$. The field $E=\mathbb F_p(\lambda_1,\dots,\lambda_s)$ is the fraction field of the polynomial ring, so the $\lambda_i$ are algebraically independent. For $\mathbb F_p$-matrices or $\mathbb F_p$-linear maps $M_i$, extended linearly over $E$,
--   $$M(\lambda)=\sum_{i=1}^s\lambda_iM_i,\qquad M(\lambda^p)=\sum_{i=1}^s\lambda_i^pM_i.$$
--
--   With $\mathcal C_D=\mathcal C_D(Q)$, the maps (21) are $M_if=([fg_ih_j])_{j=1}^t$ on $V_k$. For $g_1,\dots,g_s$ and $P$, the error-quotient map and its rank are
--   $$T_{P,k}(f)=([Pg_if])_{i=1}^s,\qquad c_P(k)=\operatorname{rank}T_{P,k}.$$
--
--   The counting quantities are
--   $$N_n(k)=\sum_{j=0}^k\binom nj,\qquad \eta=\Bigl(1-\frac1p\Bigr)\frac{N_n(K-d)}{N_n(K)},\qquad h_K=\dim V_K/\mathcal C_{\le K},$$
--   where $\mathcal C_{\le K}=\mathcal C_D\cap V_K$.
--
--   A polynomial of the form (24) is $\prod_{j=1}^t(1-q_j^{p-1})$, and the truth indicator of the predicate $h=0$ is $g_h=\mathrm{ML}(1-h^{p-1})$.
--
--   **Formalization Note** `mulMap` takes values in the quotient of the whole ring by $\mathcal C_D$, which gives a total definition: $V_D/\mathcal C_D$ embeds there because $\mathcal C_D\subseteq V_D$, so kernels and ranks are unchanged whenever the products have degree at most $D$. Ranks are `Module.finrank` of a range; the domain $V_k$ is finite dimensional, so the default value $0$ of `finrank` on infinite-dimensional spaces never occurs. `eta` uses natural subtraction $K-d$, and every theorem using it has $d\le K$.
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 2, Lemma 2.3, PDF p. 4 (printed p. 3); Section 3, eqs. (16), (21), PDF pp. 5–6 (printed pp. 4–5); Section 4, eqs. (24)–(27), (36), PDF pp. 7–8 (printed pp. 6–7); Section 5, eq. (40), PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus

namespace ResPCDegreeSize.Main

open MvPolynomial
open scoped TensorProduct

noncomputable section

/-- `E ⊗_{F_p} W`, for a subspace `W` of `F_p[x]`, as the `E`-span of its image in `E[x]`. -/
def extendScalars {n p : ℕ} (E : Type*) [Field E] [Algebra (ZMod p) E]
    (W : Submodule (ZMod p) (Poly n p)) : Submodule E (MvPolynomial (Fin n) E) :=
  Submodule.span E (MvPolynomial.map (algebraMap (ZMod p) E) '' (W : Set (Poly n p)))

/-- The field `F_p(λ₁,…,λ_s)`. -/
abbrev FpLam (p s : ℕ) := FractionRing (MvPolynomial (Fin s) (ZMod p))

/-- The indeterminate `λᵢ` in `F_p(λ₁,…,λ_s)`. -/
def lam (p : ℕ) {s : ℕ} (i : Fin s) : FpLam p s :=
  algebraMap (MvPolynomial (Fin s) (ZMod p)) (FpLam p s) (X i)

/-- The matrix `M(λ) = ∑ᵢ λᵢ Mᵢ` over `F_p(λ)`. -/
def matLam {p s : ℕ} [Fact p.Prime] {a b : Type*} (M : Fin s → Matrix a b (ZMod p)) :
    Matrix a b (FpLam p s) :=
  ∑ i, lam p i • (M i).map (algebraMap (ZMod p) (FpLam p s))

/-- The map `M(λ) = ∑ᵢ λᵢ Mᵢ`, extended linearly over `E = F_p(λ)`. -/
def mapLam {p s : ℕ} [Fact p.Prime] {U W : Type*} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup W] [Module (ZMod p) W] (M : Fin s → U →ₗ[ZMod p] W) :
    (FpLam p s ⊗[ZMod p] U) →ₗ[FpLam p s] (FpLam p s ⊗[ZMod p] W) :=
  ∑ i, lam p i • (M i).baseChange (FpLam p s)

/-- The map `M(λ^p) = ∑ᵢ λᵢ^p Mᵢ`, extended linearly over `E = F_p(λ)`. -/
def mapLamPow {p s : ℕ} [Fact p.Prime] {U W : Type*} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup W] [Module (ZMod p) W] (M : Fin s → U →ₗ[ZMod p] W) :
    (FpLam p s ⊗[ZMod p] U) →ₗ[FpLam p s] (FpLam p s ⊗[ZMod p] W) :=
  ∑ i, (lam p i ^ p) • (M i).baseChange (FpLam p s)

/-- The map `V_k → (F_p[x]/C_D)^t`, `f ↦ ([h_j f])_j`, which is `V_k → (V_D/C_D)^t` whenever
every `h_j f` has degree at most `D`, since `C_D ⊆ V_D`. -/
def mulMap {n p t : ℕ} (Q : Set (Poly n p)) (D : ℕ) (h : Fin t → Poly n p) (k : ℕ) :
    V n p k →ₗ[ZMod p] (Fin t → Poly n p ⧸ CD Q D) :=
  LinearMap.pi fun j =>
    (CD Q D).mkQ ∘ₗ LinearMap.mulLeft (ZMod p) (h j) ∘ₗ (V n p k).subtype

/-- The maps (21): `Mᵢ f = ([f gᵢ h_j])_{j=1}^t` on `V_k`. -/
def multMaps {n p s t : ℕ} (Q : Set (Poly n p)) (D : ℕ) (g : Fin s → Poly n p)
    (h : Fin t → Poly n p) (k : ℕ) (i : Fin s) :
    V n p k →ₗ[ZMod p] (Fin t → Poly n p ⧸ CD Q D) :=
  mulMap Q D (fun j => g i * h j) k

/-- The error-quotient map (25): `T_{P,k}(f) = ([P gᵢ f])ᵢ`. -/
def errorMap {n p s : ℕ} (Q : Set (Poly n p)) (D : ℕ) (g : Fin s → Poly n p) (P : Poly n p)
    (k : ℕ) : V n p k →ₗ[ZMod p] (Fin s → Poly n p ⧸ CD Q D) :=
  mulMap Q D (fun i => P * g i) k

/-- The rank (26): `c_P(k) = rank T_{P,k}`. -/
def cRank {n p s : ℕ} (Q : Set (Poly n p)) (D : ℕ) (g : Fin s → Poly n p) (P : Poly n p)
    (k : ℕ) : ℕ :=
  Module.finrank (ZMod p) (LinearMap.range (errorMap Q D g P k))

/-- (27): `N_n(k) = ∑_{j=0}^k C(n,j)`. -/
def Nn (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j

/-- (36): `η = (1 - 1/p) N_n(K-d) / N_n(K)`. -/
def eta (p n K d : ℕ) : ℝ :=
  (1 - 1 / (p : ℝ)) * ((Nn n (K - d) : ℝ) / (Nn n K : ℝ))

/-- (36): `h_K = dim V_K / C_{≤K}`, where `C_{≤K} = C_D ∩ V_K`. -/
def hDim {n p : ℕ} (Q : Set (Poly n p)) (D K : ℕ) : ℕ :=
  Module.finrank (ZMod p) (V n p K ⧸ (CD Q D).comap (V n p K).subtype)

/-- The polynomial of form (24): `∏_{j=1}^t (1 - q_j^{p-1})`. -/
def rsProduct {n p t : ℕ} (q : Fin t → Poly n p) : Poly n p :=
  ∏ j, (1 - q j ^ (p - 1))

/-- (40): the indicator `g_h = ML(1 - h^{p-1})` of the predicate `h = 0`. -/
def indicator {n p : ℕ} (h : Poly n p) : Poly n p :=
  ML (1 - h ^ (p - 1))

end

end ResPCDegreeSize.Main


