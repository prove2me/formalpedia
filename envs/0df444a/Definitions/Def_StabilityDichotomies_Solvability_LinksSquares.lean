-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_LinksSquares
-- name    : StabilityDichotomies_Solvability_LinksSquares
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:45.171767+00:00
-- url     : https://prove2.me/theorems/d239aa1f-0a93-400a-a158-8d5b4223590b
-- title:
--   Definition 3.6 — the products-of-links-and-squares instance
-- statement:
--   For a language $\Gamma$ and $N\ge1$, the instance $I_N$ has variables $x_{i,a,b}$ for $0\le i\le N$ and $a,b\in\{0,1\}$, with precisely the endpoint identifications $x_{0,a,0}=x_{0,a,1}$ and $x_{N,0,b}=x_{N,1,b}$. Let $L_i$ be its layer $i$. For every $R\in\Gamma$ of arity $r$, $a,b\in R$, $1\le j\le N$, and $\lambda\in\{j-1,j\}^r$, add one occurrence of
--
--   $$\big((x_{\lambda_1,a_1,b_1},\ldots,x_{\lambda_r,a_r,b_r}),R\big).$$
--
--   Every choice of generating data contributes separately, even when the resulting constraints coincide. This is the fixed construction used in Lemma 3.7, not an instance chosen by its desired properties.
--
--   **Formalization Note** Canonical representatives set the unused second bit to false at layer zero and the unused first bit to false at layer $N$. Internal layers retain both bits. Hence $|V_N|=4N$ even for $N=1$. A Boolean coordinate chooses one of the two consecutive layers, and nested multiset enumeration preserves all multiplicities. The definitions are total at $N=0$, where both endpoint normalizations apply and there are no constraints; the source claims are stated only for $N\ge1$.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.12, Definition 3.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Model

noncomputable section

namespace StabilityDichotomies.Solvability

open scoped Classical

/-- Canonical representatives for precisely the two endpoint identifications.
At layer 0 retain a and set b=false; at layer N retain b and set a=false.
For N≥1 these layers are disjoint and this type has 4N elements. -/
abbrev LinkVertex (N : ℕ) :=
  {p : Fin (N + 1) × Bool × Bool //
    (p.1.val = 0 → p.2.2 = false) ∧ (p.1.val = N → p.2.1 = false)}

def linkVar (N : ℕ) (i : Fin (N + 1)) (a b : Bool) : LinkVertex N :=
  ⟨(i, if i.val = N then false else a, if i.val = 0 then false else b), by
    constructor
    · intro h
      change i.val = 0 at h
      change (if i.val = 0 then false else b) = false
      exact if_pos h
    · intro h
      change i.val = N at h
      change (if i.val = N then false else a) = false
      exact if_pos h⟩

def linkLayer (N : ℕ) (i : Fin (N + 1)) : Finset (LinkVertex N) :=
  Finset.univ.filter fun v => v.val.1 = i

/-- Definition 3.6, p.12. Every generator contributes one occurrence, even if
another generator has identical scope and relation. j : Fin N represents j+1 in the paper;
λ : Fin r → Bool chooses layer j or j+1 in each coordinate. -/
def linksSquares (Γ : Language) (N : ℕ) : Instance Γ (LinkVertex N) :=
  ⟨(Finset.univ : Finset Γ.Member).val.bind fun R =>
    R.val.tuples.val.bind fun a =>
    R.val.tuples.val.bind fun b =>
    (Finset.univ : Finset (Fin N)).val.bind fun j =>
    (Finset.univ : Finset (Fin R.val.arity → Bool)).val.map fun layers =>
      ⟨R, fun t => linkVar N
        ⟨if layers t then j.val + 1 else j.val, by
          split
          · exact Nat.succ_lt_succ j.isLt
          · exact Nat.lt_succ_of_lt j.isLt⟩ (a t) (b t)⟩⟩

end StabilityDichotomies.Solvability


