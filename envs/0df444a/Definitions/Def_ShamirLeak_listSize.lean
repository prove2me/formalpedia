-- Prove2me | Definitions.Def_ShamirLeak_listSize
-- name    : ShamirLeak_listSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:53.326822+00:00
-- url     : https://prove2.me/theorems/d2195249-fd6d-4a07-9745-cbd369bb30c0
-- title:
--   The list size $\mathrm{List}_D(R,\ell)$ (Definition 9)
-- statement:
--   For a code $D\subseteq\mathbb F_p^n$, an integer radius $0\le R\le n$ and an input-list size $\ell\ge1$,
--
--   $$\mathrm{List}_D(R,\ell)=\max_{\substack{S_1,\dots,S_n\subseteq\mathbb F_p\\ |S_i|\le\ell}}\big|\{y\in D:\ |\{i:y_i\in S_i\}|\ge n-R\}\big|,$$
--
--   and $\mathrm{List}_D(R)=\mathrm{List}_D(R,1)$. Thus $\mathrm{List}_D(R,\ell)\le L$ says that every choice of input lists admits at most $L$ codewords agreeing with them in at least $n-R$ coordinates (list recovery); for $\ell=1$ this is list decoding.
--
--   List-decoding bounds for the dual code control the small-support part of the leakage distance (Lemma 14, Corollary 5, Lemma 15).
--
--   **Formalization Note** The maximum is a finite maximum (`Finset.sup`) over all tuples of lists with $|S_i|\le\ell$. For $R>n$ the natural-number subtraction makes every codeword count, which is the value of the formula with a negative agreement threshold.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 9, p.13 (PDF 15)

import Mathlib

namespace ShamirLeak

/-- The **list size** `List_D(R, ℓ)` (Definition 9, p.13 (PDF p.15)): for a code `D ⊆ 𝔽_p^n`, an
integer radius `R` and an input-list size `ℓ`,
`List_D(R, ℓ) = max_{S₁, …, Sₙ ⊆ 𝔽_p, |Sᵢ| ≤ ℓ} |{y ∈ D : |{i : yᵢ ∈ Sᵢ}| ≥ n − R}|`,
and `List_D(R) = List_D(R, 1)`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 9, p.13 (PDF p.15).

**Formalization Note.** The maximum is a `Finset.sup` over the finite set of all list tuples
`S : Fin n → Finset (ZMod p)` with `(S i).card ≤ ℓ` (the empty lists form such a tuple, so the
set is nonempty and the `sup` is a true maximum). The paper takes `0 ≤ R ≤ n`; for `R > n` the
natural-number subtraction `n − R = 0` makes every codeword count, which is the value of the
paper's formula with a negative agreement threshold. -/
noncomputable def listSize {p n : ℕ} [NeZero p] (D : Set (Fin n → ZMod p)) (R ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Fin n → Finset (ZMod p) => ∀ i, (S i).card ≤ ℓ)).sup
    (fun S => ((Finset.univ.filter (fun y : Fin n → ZMod p => y ∈ D)).filter
      (fun y => n - R ≤ (Finset.univ.filter (fun i => y i ∈ S i)).card)).card)

end ShamirLeak


