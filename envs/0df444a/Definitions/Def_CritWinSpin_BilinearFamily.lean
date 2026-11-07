-- Prove2me | Definitions.Def_CritWinSpin_BilinearFamily
-- name    : CritWinSpin_BilinearFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:27.725204+00:00
-- url     : https://prove2.me/theorems/4f4382fc-8e38-4bb6-8d7a-e9c57b20e0c5
-- title:
--   Polynomial-time generated bilinear group family and the CDH assumption
-- statement:
--   A **bilinear group family** $G(1^d)=(G,G_T,q_g,g,e)$ is given in the exponent representation: a PPT generator outputs a description $\mathrm{desc}$ on $1^d$, and for every $d\ge1$ and $\mathrm{desc}$ in the support of the generator,
--
--   1. $q=q(\mathrm{desc})$ is prime and $c\,d\le\log_2q\le C\,d$;
--   2. injective codes $\mathrm{encG},\mathrm{encT}:\mathbb Z_q\to\{0,1\}^*$ give the code of $g^a$ and of $e(g,g)^c$;
--   3. polynomial-time maps on codes realise the order, multiplication and inversion in $G$ and $G_T$, exponentiation by an integer, the pairing $e(g^a,g^b)=e(g,g)^{ab}$, and membership tests for both code sets.
--
--   The advantage of a PPT algorithm $B$ is
--   $$\mathrm{Adv}_{\mathrm{CDH}}(B)=\mathbb P\{B(1^d,g,g^a,g^b)=g^{ab}\},$$
--   over the generator's coins, uniform $a,b\in\mathbb Z_q$ and the coins of $B$. **CDH** for the family is the statement that this is negligible in $d$ for every PPT $B$.
--
--   **Formalization Note** Every prime-order cyclic $G=\langle g\rangle$ with a non-degenerate bilinear $e$ into a group of the same prime order has this form via $a\mapsto g^a$, because $e(g,g)$ generates $G_T$. Efficient group operations and membership tests are the standard reading of "polynomial-time generated", and unique codes are the usual convention. Exponents are bookkeeping indices: every map acts on codes. PPT is the published uniform `OWFLocalDesc.PPT`.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Assumption 2.3, p.10

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_OWFLocalDesc_Negligible
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc
set_option autoImplicit false

namespace CritWinSpin

/-- `desc` is a possible output of the group generator `gen` on input `1^d`. -/
def GenSupport (gen : PPT) (d : ℕ) (desc : Str) : Prop :=
  ∃ ω : Fin (gen.coins.eval (unary d).length) → Bool,
    desc = gen.alg (tupleCode [List.ofFn ω, unary d])

/-- **A polynomial-time generated bilinear group family** `G(1^d) = (G, G_T, q_g, g, e)` in the
exponent representation (Assumption 2.3, p.10).

`gen` is a PPT generator that on `1^d` outputs a description `desc` of the groups. For `desc` in
the support of `gen(1^d)`, `d ≥ 1`:
`q desc` is a prime with `log₂ q = Θ(d)`; `encG desc a` is the code of `g^a` and `encT desc c` the
code of `e(g,g)^c`, both injective; polynomial-time maps give the order, multiplication and
inversion in `G` and `G_T`, exponentiation by an integer, the pairing
`e(g^a, g^b) = e(g,g)^{ab}`, and membership tests for both code sets.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), Assumption 2.3, p.10.

**Formalization Note.** Every prime-order cyclic `G = ⟨g⟩` with a non-degenerate bilinear `e` into a
group `G_T` of the same prime order is of this form, via `a ↦ g^a`, because `e(g, g)` then generates
`G_T`; non-degeneracy is `encT 1 ≠ encT 0`, which injectivity and primality give. "Efficiently
computable" group operations and membership tests are the standard reading of "polynomial-time
generated bilinear group family", and verification (25) needs them. Unique codes are the usual
convention. The exponent `a` is a bookkeeping index only: the maps act on codes, and no field
computes a discrete logarithm. Conditions start at `d = 1` because `log₂ q = Θ(d)` is impossible
at `d = 0`. -/
structure BilinearFamily where
  /-- The generator `G(1^d)`, outputting a group description. -/
  gen : PPT
  /-- The prime order `q_g` read off a description. -/
  q : Str → ℕ
  /-- The code of `g^a`. -/
  encG : (desc : Str) → ZMod (q desc) → Str
  /-- The code of `e(g,g)^c`. -/
  encT : (desc : Str) → ZMod (q desc) → Str
  /-- The maps computing order, group operations, pairing and membership. -/
  ordF : Str → Str
  mulG : Str → Str
  invG : Str → Str
  powG : Str → Str
  mulT : Str → Str
  invT : Str → Str
  pairF : Str → Str
  memG : Str → Str
  memT : Str → Str
  ordF_poly : CookPvsNP.PolyTimeComputable ordF
  mulG_poly : CookPvsNP.PolyTimeComputable mulG
  invG_poly : CookPvsNP.PolyTimeComputable invG
  powG_poly : CookPvsNP.PolyTimeComputable powG
  mulT_poly : CookPvsNP.PolyTimeComputable mulT
  invT_poly : CookPvsNP.PolyTimeComputable invT
  pairF_poly : CookPvsNP.PolyTimeComputable pairF
  memG_poly : CookPvsNP.PolyTimeComputable memG
  memT_poly : CookPvsNP.PolyTimeComputable memT
  /-- The constants of `log₂ q = Θ(d)`. -/
  cLow : ℝ
  cHigh : ℝ
  cLow_pos : 0 < cLow
  cHigh_pos : 0 < cHigh
  prime : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → (q desc).Prime
  log_low : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc →
    cLow * (d : ℝ) ≤ Real.logb 2 (q desc : ℝ)
  log_high : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc →
    Real.logb 2 (q desc : ℝ) ≤ cHigh * (d : ℝ)
  encG_inj : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → Function.Injective (encG desc)
  encT_inj : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → Function.Injective (encT desc)
  ordF_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc →
    ordF (tupleCode [desc]) = encBin (q desc)
  mulG_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ a b : ZMod (q desc),
    mulG (tupleCode [desc, encG desc a, encG desc b]) = encG desc (a + b)
  invG_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ a : ZMod (q desc),
    invG (tupleCode [desc, encG desc a]) = encG desc (-a)
  powG_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ (a : ZMod (q desc)) (z : ℕ),
    powG (tupleCode [desc, encG desc a, encBin z]) = encG desc (a * (z : ZMod (q desc)))
  mulT_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ a b : ZMod (q desc),
    mulT (tupleCode [desc, encT desc a, encT desc b]) = encT desc (a + b)
  invT_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ a : ZMod (q desc),
    invT (tupleCode [desc, encT desc a]) = encT desc (-a)
  pairF_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ a b : ZMod (q desc),
    pairF (tupleCode [desc, encG desc a, encG desc b]) = encT desc (a * b)
  memG_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ s : Str,
    memG (tupleCode [desc, s]) = [true] ↔ s ∈ Set.range (encG desc)
  memT_spec : ∀ d, 1 ≤ d → ∀ desc, GenSupport gen d desc → ∀ s : Str,
    memT (tupleCode [desc, s]) = [true] ↔ s ∈ Set.range (encT desc)

/-- An element of `Fin q` read as an exponent in `ℤ_q`. -/
def expo {q : ℕ} (a : Fin q) : ZMod q := ((a : ℕ) : ZMod q)

/-- The CDH advantage `Adv_CDH(B) = P{B(1^d, g, g^a, g^b) = g^{ab}}` (Assumption 2.3, p.10): the
average over the coins of `gen` (giving `desc`), over uniform `a, b ∈ ℤ_q`, and over the coins of
`B`, whose input also contains the group description. -/
noncomputable def cdhAdv (F : BilinearFamily) (B : PPT) (d : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ (F.gen.coins.eval (unary d).length)) *
    ∑ ω : Fin (F.gen.coins.eval (unary d).length) → Bool,
      let desc := F.gen.alg (tupleCode [List.ofFn ω, unary d])
      (1 / ((F.q desc : ℝ) * (F.q desc : ℝ))) * ∑ a : Fin (F.q desc), ∑ b : Fin (F.q desc),
        B.prob (tupleCode [unary d, desc, F.encG desc 1, F.encG desc (expo a), F.encG desc (expo b)])
          (fun s => s = F.encG desc (expo a * expo b))

/-- **The CDH assumption** (Assumption 2.3, p.10) for the family `F`: every (uniform) PPT algorithm
`B` has negligible advantage. -/
def CDH (F : BilinearFamily) : Prop := ∀ B : PPT, Negligible (cdhAdv F B)

end CritWinSpin


