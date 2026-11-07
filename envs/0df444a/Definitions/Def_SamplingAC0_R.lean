-- Prove2me | Definitions.Def_SamplingAC0_R
-- name    : SamplingAC0_R
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:31.814456+00:00
-- url     : https://prove2.me/theorems/426a2d2e-827b-40cc-81ab-6d6e5cf515b3
-- title:
--   The hard distribution $R=(C,P)$ and invalid outputs
-- statement:
--   Let $q=2^k$. Sample $V_1,\dots,V_q$ independently and uniformly from $\mathbb F_q^2$ and record each point with $2k$ bits; $P$ is this point-list distribution. Define
--
--   $$C_\ell=\bigvee_{i=1}^{q}[V_i\in\ell],\qquad C=(C_\ell)_{\ell},\qquad R=(C,P),$$
--
--   a distribution on $b=q^2+2qk$ bits.
--
--   For an output $y=(r,p)$ of a forest with these $b$ output positions, $p_i$ is the $i$-th point decoded from the point-list bits. The output is **invalid** if there is a line $\ell$ with $r_\ell=0$ but some $i\in[q]$ with $p_i\in\ell$. Samples of $R$ are never invalid.
--
--   **Formalization Note** $R$ is defined as the law of the map sending $2qk$ uniform bits to (line bits, the bits themselves); since the encoding is a bijection, uniform bits encode independent uniform points.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8 (the hard distribution; invalid outputs, proof intuition)

import Mathlib
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_lineDNF
set_option autoImplicit false

namespace SamplingAC0

/-- **The hard distribution `R = (C, P)`.** Riazanov–Viola, *Sampling Tools and the Power of AC0*,
STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8: "Sample V_1, . . . , V_q ∼ F_q²
independently. Record each point using 2k bits. Write P for this point-list distribution and define
C_ℓ := ⋁_{i=1}^{q} [V_i ∈ ℓ], C := (C_ℓ)_ℓ, R := (C, P), m := 2qk, b := q² + m."

`R enc k` is the law, for `2qk` uniform input bits encoding `q` independent uniform points
`V_1, …, V_q`, of the vector whose line coordinate `ℓ` is `C_ℓ = [∃ i, V_i ∈ ℓ]` and whose
point-list coordinates are the input bits themselves.

**Formalization Note.** Points are recorded with the encoding `enc k` of each coordinate; for
`k ≥ 1` it is a bijection, so uniform bits give independent uniform points. -/
noncomputable def R (enc : Encoding) (k : ℕ) : PMF (ROut k → Bool) :=
  law (fun x : RIn k → Bool => fun o => match o with
    | Sum.inl ℓ => decide (∃ i, onLine ℓ (decodePt enc x i))
    | Sum.inr p => x p)

/-- The `i`-th listed point `p_i` read from the point-list part of an output vector `y`
(the value `g_i` of the forest's point trees). -/
noncomputable def decodeOut (enc : Encoding) {k : ℕ} (y : ROut k → Bool) (i : Fin (2 ^ k)) : F k × F k :=
  decodePt enc (fun p => y (Sum.inr p)) i

/-- **Invalid outputs.** §3, p.8: "f(U) =: (r, p) is invalid in the following sense: there exists
ℓ ∈ L such that r_ℓ = 0, but there is i ∈ [q] with p_i ∈ ℓ." -/
def Invalid (enc : Encoding) {k : ℕ} (y : ROut k → Bool) : Prop :=
  ∃ ℓ : Line k, y (Sum.inl ℓ) = false ∧ ∃ i, onLine ℓ (decodeOut enc y i)

end SamplingAC0


