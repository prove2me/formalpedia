-- Prove2me | Definitions.Def_bananaF1Classes
-- name    : bananaF1Classes
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T16:18:09.871389+00:00
-- url     : https://prove2.me/theorems/3c2731ae-a499-42b7-8777-34a896b812b9
-- title:
--   Grothendieck classes of banana graph hypersurfaces in $\mathbb{T} = \mathbb{L} - 1$
-- statement:
--   Polynomial models, in $\mathbb{Z}[\mathbb{T}]$ with $\mathbb{T} = [\mathbb{G}_m] = \mathbb{L} - 1$, of the Grothendieck classes attached to the banana graph $\Gamma_n$ (two vertices joined by $n$ parallel edges).
--
--   Four polynomials are defined for a parameter $n \in \mathbb{N}$:
--
--   - $[\mathbb{P}^{n-1}] = \sum_{k=1}^{n} \binom{n}{k} \mathbb{T}^{k-1}$, the polynomial representative of $((1+\mathbb{T})^n - 1)/\mathbb{T}$ used in equation (3.9) of the source;
--   - the alternating polynomial $\sum_{j=0}^{n-1} (-1)^{n-1-j} \mathbb{T}^j$, the representative of $(\mathbb{T}^n - (-1)^n)/(\mathbb{T}+1)$ used in equation (3.10);
--   - the class of the hypersurface complement, $[Y_{\Gamma_n}] = (\mathbb{T}^n - (-1)^n)/(\mathbb{T}+1) + n\,\mathbb{T}^{n-2}$;
--   - the class of the graph hypersurface itself, $[X_{\Gamma_n}] = [\mathbb{P}^{n-1}] - [Y_{\Gamma_n}]$, which is equation (3.8) of the source.
--
--   Nothing about torifications, tori or the Grothendieck ring is formalized here: the closed formula of the source is taken as given and turned into explicit polynomials, so that the positivity statements of Lemma 3.9 become statements about their coefficients. All index subtractions are truncated natural subtraction, so the definitions are only intended to model the source for $n \ge 3$.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Mathlib

namespace BananaF1

open Polynomial

/-- The class of `Pⁿ⁻¹` written in the variable `T = [𝔾ₘ] = L - 1`:
the polynomial `∑_{k=1}^{n} C(n,k) T^{k-1}`, a representative of `((1+T)ⁿ - 1)/T`. -/
noncomputable def bananaProjClass (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range n, C ((n.choose (k + 1) : ℤ)) * X ^ k

/-- The alternating polynomial `∑_{j=0}^{n-1} (-1)^{n-1-j} T^j`,
a representative of `(Tⁿ - (-1)ⁿ)/(T+1)`. -/
noncomputable def bananaTail (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range n, C ((-1 : ℤ) ^ (n - 1 - j)) * X ^ j

/-- The class `[Y_{Γₙ}]` of the complement of the banana graph hypersurface,
`(Tⁿ - (-1)ⁿ)/(T+1) + n Tⁿ⁻²`. -/
noncomputable def bananaComplementClass (n : ℕ) : Polynomial ℤ :=
  bananaTail n + C (n : ℤ) * X ^ (n - 2)

/-- The class `[X_{Γₙ}]` of the banana graph hypersurface, `[Pⁿ⁻¹] - [Y_{Γₙ}]`. -/
noncomputable def bananaHypersurfaceClass (n : ℕ) : Polynomial ℤ :=
  bananaProjClass n - bananaComplementClass n

end BananaF1


