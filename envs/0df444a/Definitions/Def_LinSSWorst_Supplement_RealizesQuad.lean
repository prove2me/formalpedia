-- Prove2me | Definitions.Def_LinSSWorst_Supplement_RealizesQuad
-- name    : LinSSWorst_Supplement_RealizesQuad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:43:40.442686+00:00
-- url     : https://prove2.me/theorems/c3813e82-6a2e-4983-a693-5fa1a5172e89
-- title:
--   Secret-sharing schemes over $\mathbb F_2$ with quadratic sharing and reconstruction
-- statement:
--   A secret-sharing scheme for one-bit secrets over $\mathbb F_2$ has secret $s\in\mathbb F_2$, random string $r\in\mathbb F_2^{\ell_r}$, and gives party $P_i$ a share in $\mathbb F_2^{\ell_i}$. It has **quadratic sharing and reconstruction** if
--   1. every coordinate of every share is the value at $(s,r)$ of a polynomial over $\mathbb F_2$ of total degree at most $2$ in the $1+\ell_r$ variables $s,r_1,\dots,r_{\ell_r}$, and
--   2. for every authorized coalition $x$ (with $f(x)=1$) there is a polynomial $\mathrm{Recon}_x$ of total degree at most $2$ in the coordinates of the coalition's shares with $\mathrm{Recon}_x(\Pi_x(s;r))=s$ for all $s,r$.
--
--   It **realizes** $f$ if in addition it is private: for every $x$ with $f(x)=0$ and all $s,s'$, the views $\Pi_x(s;r)$ and $\Pi_x(s';r)$ have the same distribution for uniform $r$. Its total share size is $\sum_i\ell_i$ bits.
--
--   These are the quadratic schemes of [BOP21] used in Theorems 1.6 and 6.2.
--
--   **Formalization Note** Share coordinates are `MvPolynomial (Option (Fin ℓr)) (ZMod 2)` with `none` the secret variable; degrees are `totalDegree` of the given polynomial representatives. The reconstruction polynomial's variables are pairs (party of the coalition, share coordinate).
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), p.5 (definition of quadratic schemes, [BOP21]); Definition A.2, p.29

import Mathlib
import Definitions.Def_LinSSWorst_Supplement_RealizesGen

namespace LinSSWorst.Supplement

/-- The share vector of a **polynomial secret-sharing scheme** over `F₂` (p.5, [BOP21]; Definition A.2,
p.29), from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…). The secret is `s ∈ F₂`, the random string is
`r ∈ F₂^{ℓ_r}`, and party `i` receives `ℓ_i` elements of `F₂`; coordinate `c` of party `i`'s share is the
value at `(s, r)` of the polynomial `sh i c` in the `1 + ℓ_r` variables `(s, r_1, …, r_{ℓ_r})`.

**Formalization Note.** `F₂` is `ZMod 2`. The polynomial variables are `Option (Fin ℓr)`: `none` is the
secret `s` and `some j` is the random element `r_j`. -/
noncomputable def quadShares {n ℓr : ℕ} {ℓ : Fin n → ℕ}
    (sh : (i : Fin n) → Fin (ℓ i) → MvPolynomial (Option (Fin ℓr)) (ZMod 2))
    (s : ZMod 2) (r : Fin ℓr → ZMod 2) : (i : Fin n) → Fin (ℓ i) → ZMod 2 :=
  fun i c => MvPolynomial.eval (fun v : Option (Fin ℓr) => v.elim s r) (sh i c)

/-- A secret-sharing scheme **with quadratic sharing and reconstruction** over `F₂` for one-bit secrets
**realizes** the access structure `f` (p.5: "both sharing and reconstruction are computed by polynomials of
degree at most two over the same field [BOP21]"; Definition A.2, p.29):
1. (quadratic sharing) every share coordinate `sh i c` is a polynomial of total degree at most two in the
   secret and the random elements;
2. (correctness with quadratic reconstruction) for every `x` with `f(x) = 1` there is a polynomial
   `Recon_x` of total degree at most two in the coordinates of the coalition's shares with
   `Recon_x(Π_x(s; r)) = s` for every `s ∈ F₂` and every `r ∈ F₂^{ℓ_r}`;
3. (privacy) for every `x` with `f(x) = 0` and all `s, s' ∈ F₂`, the distributions of `Π_x(s; r)` and
   `Π_x(s'; r)` for `r` uniform on `F₂^{ℓ_r}` are identical.

The total share size of such a scheme is `Σ_i ℓ_i` bits (`|S_i| = 2^{ℓ_i}`).

**Formalization Note.** The reconstruction polynomial's variables are the pairs `⟨j, c⟩` with `j` a party
of the coalition and `c` one of its share coordinates. Degrees are `MvPolynomial.totalDegree`; a
polynomial over `F₂` is a formal polynomial, so "degree at most two" asks for some representative of
degree at most two. Privacy is equality of the push-forwards of the uniform law on `Fin ℓr → ZMod 2`. -/
def RealizesQuad {n ℓr : ℕ} {ℓ : Fin n → ℕ} (f : (Fin n → Bool) → Bool)
    (sh : (i : Fin n) → Fin (ℓ i) → MvPolynomial (Option (Fin ℓr)) (ZMod 2)) : Prop :=
  (∀ i c, (sh i c).totalDegree ≤ 2) ∧
  (∀ x : Fin n → Bool, f x = true →
    ∃ recon : MvPolynomial (Σ j : {j : Fin n // x j = true}, Fin (ℓ j.1)) (ZMod 2),
      recon.totalDegree ≤ 2 ∧
      ∀ (s : ZMod 2) (r : Fin ℓr → ZMod 2),
        MvPolynomial.eval (fun p => quadShares sh s r p.1.1 p.2) recon = s) ∧
  (∀ x : Fin n → Bool, f x = false → ∀ s s' : ZMod 2,
    (PMF.uniformOfFintype (Fin ℓr → ZMod 2)).map (fun r => viewGen x (quadShares sh s r)) =
      (PMF.uniformOfFintype (Fin ℓr → ZMod 2)).map (fun r => viewGen x (quadShares sh s' r)))

end LinSSWorst.Supplement


