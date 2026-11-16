-- Prove2me | Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable
-- name    : RSSubspaceDesign_Supplement_IsCurveDecodable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:35:35.434844+00:00
-- url     : https://prove2.me/theorems/823939fc-9d7d-4fec-ac4c-8fedb6ae45e6
-- title:
--   $(\ell, \delta, a, b)$-$E$-curve decodability
-- statement:
--   Let $E$ be a field, $\Sigma$ an $E$-vector space and $C \subseteq \Sigma^n$ an $E$-linear code. The code $C$ is **$(\ell, \delta, a, b)$-$E$-curve-decodable** if, for all $u_0, \dots, u_\ell \in \Sigma^n$ and every function $f : E \to C$, whenever the set
--
--   $$
--   A = \Bigl\{\alpha \in E : \Delta\Bigl(\sum_{j=0}^{\ell} u_j \alpha^j,\ f(\alpha)\Bigr) \le \delta\Bigr\}
--   $$
--
--   has at least $a$ elements, there are codewords $c_0, \dots, c_\ell \in C$ such that
--
--   $$
--   \Bigl|\Bigl\{\alpha \in A : f(\alpha) = \sum_{j=0}^{\ell} c_j \alpha^j\Bigr\}\Bigr| \ge b .
--   $$
--
--   For $\ell = 1$ this is **line decodability**; the paper writes $(\delta, a, b)$-$F$-line-decodable for $(1, \delta, a, b)$-$F$-curve-decodable. If many points of a degree-$\ell$ curve are close to codewords, then many of those codewords lie on one codeword curve. This notion underlies proximity gaps and correlated agreement.
--
--   **Formalization Note** $C$ is an $E$-submodule of $\Sigma^n$; a code over an extension field $F$ is viewed over a subfield $K$ by restriction of scalars, with $\alpha \in K$ acting through $K \to F$. The threshold $a$ is a natural number and $b$ is real; $|\cdot| \ge b$ is written $\lceil b\rceil \le |\cdot|$, which is equivalent because sizes are integers. Sizes are `Set.encard`.
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Definition 2.8, p.12 (and p.42 for line decodability)

import Mathlib
import Definitions.Def_RSSubspaceDesign_Supplement_relDist

namespace RSSubspaceDesign

namespace Supplement

/-- **Definition 2.8 (Curve decodability).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Definition 2.8, p.12; line decodability is `ℓ = 1` (p.12, and
p.42: "`(δ, a, b)`-F-line-decodable for `(1, δ, a, b)`-F-curve-decodable").

Let `E` be a field and `C ⊆ Σⁿ` an `E`-linear code. `C` is `(ℓ, δ, a, b)`-`E`-curve-decodable if,
for every `u₀, …, u_ℓ ∈ Σⁿ` and every function `f : E → C`, whenever the set
`A = {α ∈ E : Δ(∑_{j=0}^{ℓ} uⱼ αʲ, f(α)) ≤ δ}` has at least `a` elements, there exist
`c₀, …, c_ℓ ∈ C` such that `|{α ∈ A : f(α) = ∑_{j=0}^{ℓ} cⱼ αʲ}| ≥ b`.

**Formalization Note.** `C` is a `Submodule E (Fin n → Σ)` for any `E`-module `Σ` (the paper's
`K`-additive code over `Σ = Kˢ` or `Σ = F`); a code over an extension `F` is viewed over a subfield
`K` by `restrictScalars`. Indices `j` run over `Fin (ℓ + 1)`. Sizes are `Set.encard`, so infinite
sets take no junk value. The threshold `a` is a natural number; `b` is real (Theorem 8.1 uses
`aε²/4`), and "`|·| ≥ b`" is `⌈b⌉₊ ≤ |·|`, which is equivalent because the size is an integer (and
holds trivially for `b ≤ 0`, as `|·| ≥ b` does). -/
def IsCurveDecodable (E : Type*) {Sig : Type*} [Field E] [AddCommGroup Sig] [Module E Sig]
    {n : ℕ} (C : Submodule E (Fin n → Sig)) (ℓ : ℕ) (δ : ℝ) (a : ℕ) (b : ℝ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → Fin n → Sig) (f : E → C),
    (a : ℕ∞) ≤ {α : E | relDist (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j) (f α : Fin n → Sig) ≤ δ}.encard →
    ∃ c : Fin (ℓ + 1) → C,
      (⌈b⌉₊ : ℕ∞) ≤
        {α : E | relDist (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j) (f α : Fin n → Sig) ≤ δ ∧
          (f α : Fin n → Sig) = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (c j : Fin n → Sig)}.encard

end Supplement

end RSSubspaceDesign


