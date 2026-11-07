-- Prove2me | Definitions.Def_TimeSpaceMA_RoundAccepts
-- name    : TimeSpaceMA_RoundAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:59:07.857075+00:00
-- url     : https://prove2.me/theorems/19885fba-75ca-4357-ad06-d23514e0fbf6
-- title:
--   One round of the trace test
-- statement:
--   Given $U$ and tables $W:[L]^m\to\mathbb Z^d$ and $R_j:[L]^{m-j}\times[L]^{m-j}\to\mathbb Z$ for $1\le j\le m-1$, a round at the anchor $(a,b)\in[L]^m\times[L]^m$ accepts if:
--
--   1. all $m$ lines of $W$ through $a$ are codewords of $G$ over $\mathbb Z^d$, and for each $1\le j\le m-1$ all $2(m-j)$ lines of $R_j$ through $(a_{>j},b_{>j})$ are codewords of $G$ over $\mathbb Z$;
--   2. for each $1\le j\le m-1$, $R_j(\alpha,\beta)=\sum_{\ell\in[q]}R_{j-1}(\sigma(\ell)\alpha,\sigma(\ell)\beta)$ at $(\alpha,\beta)=(a_{>j},b_{>j})$, where for $j=1$ the values $R_0$ are computed as $\Phi(Y(\cdot),Y(\cdot))$ with $Y=(W,U)$;
--   3. $\sum_{\ell\in[q]}R_{m-1}(\sigma(\ell),\sigma(\ell))=0$.
--
--   The rejection probability is taken over a uniform anchor.
--
--   **Formalization Note** $R_j$ is `R n` with $n=m-j$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 3.18, p.14

import Definitions.Def_TimeSpaceMA_honestTable

namespace TimeSpaceMA

variable {q L m d e : ℕ}

/-- `a_{>j} = (a_{j+1}, …, a_m)`, written through the number `n = m − j` of its coordinates; p.7. -/
def lastN {X : Type*} (a : Fin m → X) (n : ℕ) (hn : n ≤ m) : Fin n → X :=
  fun i => a ⟨m - n + i.val, by omega⟩

/-- The table `R_{j−1}` at level `n + 1 = m − (j − 1)`. For `j = 1` (that is `n + 1 = m`) its values are
computed as `Φ(Y(·), Y(·))`; otherwise they are entries of the given table. Definition 3.18, step 3,
p.14. -/
def levelBelow (Y : (Fin m → Fin L) → (Fin d ⊕ Fin e → ℤ))
    (Φ : (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] ℤ)
    (R : (n : ℕ) → (Fin n → Fin L) → (Fin n → Fin L) → ℤ) (n : ℕ)
    (α β : Fin (n + 1) → Fin L) : ℤ :=
  if h : n + 1 = m then Φ (Y (α ∘ Fin.cast h.symm)) (Y (β ∘ Fin.cast h.symm))
  else R (n + 1) α β

/-- One round of the trace test accepts at the anchor `(a, b)` (Williams, Xi, STOC 2027 submission,
manuscript sha256 184c2f95…, Definition 3.18, p.14): the line tests of step 2, the trace checks of
step 3 and the final check of step 4 all pass.

**Formalization Note** `U` and `W` are the oracles; `Y(α) = (W(α), U(α))`. The table `R_j` is `R n` with
`n = m − j`, so `1 ≤ j ≤ m − 1` is `1 ≤ n` and `n + 1 ≤ m`, and `R_{m−1}` is `R 1`. Entries of `R n`
outside that range are never read. -/
def RoundAccepts (G : SubsetSumCode q L) (σ : Fin q → Fin L)
    (Φ : (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] ℤ)
    (U : (Fin m → Fin L) → Fin e → ℤ) (W : (Fin m → Fin L) → Fin d → ℤ)
    (R : (n : ℕ) → (Fin n → Fin L) → (Fin n → Fin L) → ℤ)
    (a b : Fin m → Fin L) : Prop :=
  (∀ i, G.IsCodeword (line W a i)) ∧
  (∀ (n : ℕ) (_hn : 1 ≤ n) (hn' : n + 1 ≤ m),
    let α := lastN a n (by omega)
    let β := lastN b n (by omega)
    (∀ i, G.IsCodeword (line (fun α' => R n α' β) α i) ∧
        G.IsCodeword (line (fun β' => R n α β') β i)) ∧
      R n α β = ∑ ℓ : Fin q,
        levelBelow (fun γ => Sum.elim (W γ) (U γ)) Φ R n
          (Fin.cons (σ ℓ) α) (Fin.cons (σ ℓ) β)) ∧
  ∑ ℓ : Fin q, R 1 (fun _ => σ ℓ) (fun _ => σ ℓ) = 0

open Classical in
/-- The probability that a round rejects, over a uniform anchor `(a, b) ∈ [L]^m × [L]^m`. -/
noncomputable def traceReject (G : SubsetSumCode q L) (σ : Fin q → Fin L)
    (Φ : (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] (Fin d ⊕ Fin e → ℤ) →ₗ[ℤ] ℤ)
    (U : (Fin m → Fin L) → Fin e → ℤ) (W : (Fin m → Fin L) → Fin d → ℤ)
    (R : (n : ℕ) → (Fin n → Fin L) → (Fin n → Fin L) → ℤ) : ℝ :=
  ((Finset.univ.filter fun ab : (Fin m → Fin L) × (Fin m → Fin L) =>
      ¬ RoundAccepts G σ Φ U W R ab.1 ab.2).card : ℝ) / (L : ℝ) ^ (2 * m)

end TimeSpaceMA


