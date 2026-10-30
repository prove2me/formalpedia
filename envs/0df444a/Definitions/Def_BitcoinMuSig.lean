-- Prove2me | Definitions.Def_BitcoinMuSig
-- name    : BitcoinMuSig
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-30T00:25:48.321153+00:00
-- url     : https://prove2.me/theorems/b387cdc0-9cdc-4ca1-a55b-199565ba2027
-- title:
--   secp256k1 as a Mathlib elliptic curve, the bridge from the executable curve, and BIP327 MuSig2 session algorithms
-- statement:
--   Over Mathlib and the signature and Taproot missions.
--
--   **Primality.** `powMod_eq`, `prime_of_cert` (a Lucas–Pratt certificate checker) and `p_prime_cert : Nat.Prime p` with the instance `Fact (Nat.Prime p)`: the field prime of secp256k1 is certified, so `ZMod p` is a field. **`W`** — the curve $y^2 = x^3 + 7$ over `ZMod p` as a Mathlib `WeierstrassCurve.Affine`, with discriminant $-21168 \ne 0$ and `nonsingular_of_onCurve`.
--
--   **The bridge.** **`toPoint`**, **`tp`** — the executable point (an optional pair of naturals) as a Mathlib point (`0` for infinity); **`Valid P`** — on the curve; **`Reduced P`** — coordinates below $p$; **`ofPoint`**, **`Gpt`** (the generator as a Mathlib point), **`pneg`**, **`hasEvenY`**, **`evenY`**.
--
--   **BIP327.** **`tagged`**, **`xbytes`** (32-byte x-coordinate), **`cbytes`** (33-byte compressed point), **`cpoint`** (parse a compressed point), **`KeyAggCtx`** (aggregate point, `gacc`, `tacc`), **`hashKeys`**, **`getSecondKey`**, **`keyAggCoeffInternal`**, **`keyAggCoeff`**, **`keyAggSum`**, **`keyAgg`**, **`applyTweak`**, **`applyTweaks`**, **`keyAggTweaked`**, **`nonceSum`**, **`nonceAgg`**, **`SessionCtx`**, **`SessionValues`**, **`getSessionValues`**, **`partialSigVerifyInternal`**, **`partialSigAgg`** — the BIP's algorithms over byte strings and the executable curve, including the second-key exception, plain and x-only tweaks, the negations for odd `Q.y` and `R.y`, and the substitution $R = G$ at infinity.
--
--   **FROST.** **`lagrangeCoeff S i`** — the Lagrange coefficient at 0 for identifier set $S$, in `ZMod n`.
--
--   **Formalization Note.** Imports Mathlib, `BitcoinSig`, `BitcoinTaproot`. The file carries the primality certificate and the curve's nonsingularity as lemmas because Mathlib's group structure on points needs them; they are checked by `decide +kernel`, never `native_decide`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Mathlib
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinTaproot

/-!
# MuSig2 (BIP327) over secp256k1, bridged to Mathlib's Weierstrass group law

Two layers.

* **The bridge.** `W` is secp256k1 (`y² = x³ + 7`) as a `WeierstrassCurve.Affine (ZMod p)`.
  `toPoint` sends an executable point of `Def_BitcoinSig` (`none` = infinity, `some (x, y)` with
  `onCurve`) to a Mathlib point; `tp` is its total version (off-curve data maps to `0`) and
  `ofPoint` the canonical representative (coordinates reduced below `p`). The theorems of the
  mission show that `padd`, `pmul`, `pneg` are Mathlib's `+`, `•`, `-` through this map. The group
  law needs `ZMod p` to be a field, so `Nat.Prime p` is certified here once and for all by a
  Lucas–Pratt certificate (`p - 1 = 2 · 3 · 7 · 13441 · q₅`, recursively), with the modular
  exponentiations kernel-checked through the executable `powMod` of `Def_BitcoinSig`.
* **MuSig2.** Executable transcription of BIP327's `KeyAgg`, `ApplyTweak`, `NonceAgg`,
  `GetSessionValues`, `PartialSigVerifyInternal` and `PartialSigAgg` on the byte strings and
  executable points of `Def_BitcoinSig` (`cpoint`/`cbytes` are the 33-byte compressed encodings,
  tagged hashes are `BitcoinSig.taggedHash`).
-/

namespace BitcoinMuSig

open BitcoinSer (Byte Bytes)
open BitcoinSig (p n Point G Gx Gy onCurve padd pmul powMod powModAux finv liftX liftXParity beVal)

/-! ### `powMod` computes modular powers -/

theorem powModAux_eq (m : ℕ) : ∀ (fuel b e acc : ℕ), e < 2 ^ fuel → acc % m = acc →
    powModAux m fuel b e acc = acc * b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he hacc
    have h0 : e = 0 := by simpa using he
    subst h0
    simp [powModAux, hacc]
  | succ f ih =>
    intro b e acc he hacc
    have he' : e / 2 < 2 ^ f := by
      rw [pow_succ] at he; omega
    have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
    have hpow : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      conv_lhs => rw [hsplit]
      rw [pow_add, pow_mul, pow_two]
    have hbb : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
    simp only [powModAux]
    split_ifs with h0 h1
    · subst h0; simp [hacc]
    · rw [ih _ _ _ he' (Nat.mod_mod _ _)]
      have : acc * b % m * (b * b % m) ^ (e / 2) ≡ acc * (b ^ e) [MOD m] := by
        rw [hpow, h1, pow_one]
        calc acc * b % m * (b * b % m) ^ (e / 2) ≡ acc * b * (b * b) ^ (e / 2) [MOD m] :=
              (Nat.mod_modEq _ _).mul hbb
          _ = acc * ((b * b) ^ (e / 2) * b) := by ring
      exact this
    · rw [ih _ _ _ he' hacc]
      have h2 : e % 2 = 0 := by omega
      have : acc * (b * b % m) ^ (e / 2) ≡ acc * (b ^ e) [MOD m] := by
        rw [hpow, h2, pow_zero, mul_one]
        exact hbb.mul_left _
      exact this

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  unfold powMod
  rw [powModAux_eq m (e + 1) (b % m) e (1 % m) (by
      have := Nat.lt_two_pow_self (n := e); calc e < 2 ^ e := this
        _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.mod_mod _ _)]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod, one_mul]

/-! ### A Lucas–Pratt primality certificate -/

/-- One Pratt step: `q` is prime if `a ^ (q-1) ≡ 1`, and `a ^ ((q-1)/r) ≢ 1` for every prime
factor `r` of `q - 1` (listed with multiplicity in `fs`). -/
theorem prime_of_cert (q a : ℕ) (fs : List ℕ) (hq : 1 < q) (hfs : ∀ r ∈ fs, Nat.Prime r)
    (hprod : q - 1 = fs.prod) (ha : powMod a (q - 1) q = 1)
    (hb : ∀ r ∈ fs, powMod a ((q - 1) / r) q ≠ 1) : Nat.Prime q := by
  rw [powMod_eq] at ha
  apply lucas_primality q (a : ZMod q)
  · have h2 : ((a ^ (q - 1) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff', ha, Nat.one_mod_eq_one.mpr (by omega)]
    push_cast at h2
    exact h2
  · intro r hr hdvd h1
    have hmem : r ∈ fs := by
      rw [hprod] at hdvd
      obtain ⟨r', hr', hrr'⟩ := (Nat.prime_iff.mp hr).dvd_prod_iff.mp hdvd
      rwa [(Nat.prime_dvd_prime_iff_eq hr (hfs r' hr')).mp hrr']
    apply hb r hmem
    have h2 : ((a ^ ((q - 1) / r) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      push_cast
      exact h1
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [powMod_eq, h2, Nat.one_mod_eq_one.mpr (by omega)]

set_option maxRecDepth 100000 in
private theorem prime_13331831 : Nat.Prime 13331831 := by norm_num

set_option maxRecDepth 100000 in
private theorem prime_173378833005251801 : Nat.Prime 173378833005251801 := by
  refine prime_of_cert _ 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831] (by norm_num) ?_ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime_13331831 | norm_num

set_option maxRecDepth 100000 in
private theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  refine prime_of_cert _ 5 [2, 2, 2, 3, 5323, 173378833005251801] (by norm_num) ?_ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime_173378833005251801 | norm_num

set_option maxRecDepth 100000 in
private theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  refine prime_of_cert _ 6 [2, 3, 22149492674086928081353] (by norm_num) ?_ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> first | exact prime_22149492674086928081353 | norm_num

set_option maxRecDepth 100000 in
private theorem prime_1206781 : Nat.Prime 1206781 := by norm_num

set_option maxRecDepth 100000 in
private theorem prime_7240687 : Nat.Prime 7240687 := by
  refine prime_of_cert _ 3 [2, 3, 1206781] (by norm_num) ?_ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> first | exact prime_1206781 | norm_num

set_option maxRecDepth 100000 in
private theorem prime_107590001 : Nat.Prime 107590001 := by
  refine prime_of_cert _ 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53] (by norm_num) ?_ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

set_option maxRecDepth 100000 in
private theorem prime_255515944373312847190720520512484175977 :
    Nat.Prime 255515944373312847190720520512484175977 := by
  refine prime_of_cert _ 3 [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 96557, 41201, 107590001, 7240687]
    (by norm_num) ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact prime_107590001 | exact prime_7240687 | norm_num

set_option maxRecDepth 100000 in
private theorem prime_q5 :
    Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  refine prime_of_cert _ 10 [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119,
    255515944373312847190720520512484175977]
    (by norm_num) ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact prime_132896956044521568488119
      | exact prime_255515944373312847190720520512484175977
      | norm_num

set_option maxRecDepth 100000 in
/-- `p = 2^256 - 2^32 - 977` is prime (Lucas–Pratt certificate with witness `3`,
`p - 1 = 2 · 3 · 7 · 13441 · 205115282021455665897114700593932402728804164701536103180137503955397371`). -/
theorem p_prime_cert : Nat.Prime p := by
  refine prime_of_cert _ 3 [2, 3, 7, 13441,
    205115282021455665897114700593932402728804164701536103180137503955397371]
    (by decide) ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> first | exact prime_q5 | norm_num

instance instFactPrimeP : Fact (Nat.Prime p) := ⟨p_prime_cert⟩

/-! ### secp256k1 as a Mathlib Weierstrass curve -/

/-- secp256k1: `y² = x³ + 7` over `𝔽_p` (`a₁ = a₂ = a₃ = a₄ = 0`, `a₆ = 7`). -/
def W : WeierstrassCurve.Affine (ZMod p) := ⟨0, 0, 0, 0, 7⟩

theorem W_Δ : W.Δ = -21168 := by
  simp [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num

theorem W_Δ_ne_zero : W.Δ ≠ 0 := by
  rw [W_Δ, neg_ne_zero, show (21168 : ZMod p) = ((21168 : ℕ) : ZMod p) by norm_cast, Ne,
    ZMod.natCast_eq_zero_iff]
  decide

/-- The executable curve test is Mathlib's equation. -/
theorem equation_iff_onCurve (x y : ℕ) :
    W.Equation (x : ZMod p) (y : ZMod p) ↔ onCurve (x, y) = true := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W, onCurve, decide_eq_true_eq]
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem nonsingular_of_onCurve {x y : ℕ} (h : onCurve (x, y) = true) :
    W.Nonsingular (x : ZMod p) (y : ZMod p) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero W_Δ_ne_zero).mp
    ((equation_iff_onCurve x y).mpr h)

/-- The Mathlib point of an executable point: `none` (infinity) ↦ `0`; `some (x, y)` ↦ the affine
point `(x mod p, y mod p)` if it is on the curve, and no point otherwise. -/
def toPoint : Point → Option W.Point
  | none => some 0
  | some (x, y) =>
    if h : onCurve (x, y) = true then
      some (.some (x : ZMod p) (y : ZMod p) (nonsingular_of_onCurve h))
    else none

/-- The total version of `toPoint` (data off the curve maps to `0`). -/
def tp (P : Point) : W.Point := (toPoint P).getD 0

/-- An executable point whose affine data (if any) lies on the curve. -/
def Valid (P : Point) : Prop := ∀ x y, P = some (x, y) → onCurve (x, y) = true

/-- An executable point whose coordinates (if any) are reduced below `p`. -/
def Reduced (P : Point) : Prop := ∀ x y, P = some (x, y) → x < p ∧ y < p

/-- The canonical executable representative of a Mathlib point. -/
def ofPoint : W.Point → Point
  | .zero => none
  | .some x y _ => some (x.val, y.val)

/-- The generator `G` as a Mathlib point. -/
def Gpt : W.Point := .some (Gx : ZMod p) (Gy : ZMod p) (nonsingular_of_onCurve (by decide))

/-- Executable negation `-(x, y) = (x, -y)`. -/
def pneg : Point → Point
  | none => none
  | some (x, y) => some (x, (p - y % p) % p)

/-- `has_even_y` of BIP340/BIP327 on affine data. -/
def hasEvenY (P : ℕ × ℕ) : Bool := decide (P.2 % 2 = 0)

/-- `has_even_y` on Mathlib points (infinity counts as even). -/
def evenY : W.Point → Bool
  | .zero => true
  | .some _ y _ => decide (y.val % 2 = 0)

/-! ### MuSig2 (BIP327): executable transcription -/

/-- `tagged_hash` with a string tag. -/
def tagged (tag : String) (m : Bytes) : Bytes := BitcoinSig.taggedHash (BitcoinSig.ascii tag) m

/-- `xbytes(P)`: the 32-byte big-endian abscissa. -/
def xbytes (P : ℕ × ℕ) : Bytes := BitcoinTaproot.be32 P.1

/-- `cbytes(P)`: compressed encoding `02/03 || xbytes(P)`. -/
def cbytes (P : ℕ × ℕ) : Bytes := (if hasEvenY P then 2 else 3) :: xbytes P

def zero33 : Bytes := List.replicate 33 0

/-- `cbytes_ext`: infinity is encoded as 33 zero bytes. -/
def cbytesExt : Point → Bytes
  | none => zero33
  | some P => cbytes P

/-- `cpoint(x)`: parse a 33-byte compressed point (`none` = failure). -/
def cpoint (b : Bytes) : Option (ℕ × ℕ) := if b.length = 33 then BitcoinSig.parsePubkey b else none

/-- `cpoint_ext(x)`: `none` = failure, `some none` = infinity. -/
def cpointExt (b : Bytes) : Option Point :=
  if b = zero33 then some none else (cpoint b).map some

/-- `KeyAggContext(Q, gacc, tacc)`; `Q` is never infinity. -/
structure KeyAggCtx where
  Q : ℕ × ℕ
  gacc : ℕ
  tacc : ℕ
  deriving Repr, DecidableEq

/-- `HashKeys(pk_1..pk_u) = hash_KeyAgg list(pk_1 || ... || pk_u)`. -/
def hashKeys (pks : List Bytes) : Bytes := tagged "KeyAgg list" pks.flatten

/-- `GetSecondKey`: the first key different from the first one, else `bytes(33, 0)`. -/
def getSecondKey (pks : List Bytes) : Bytes :=
  match pks with
  | [] => zero33
  | pk1 :: _ => (pks.find? (fun pk => pk ≠ pk1)).getD zero33

/-- `KeyAggCoeffInternal(pk_1..pk_u, pk', pk2)`. -/
def keyAggCoeffInternal (pks : List Bytes) (pk pk2 : Bytes) : ℕ :=
  if pk = pk2 then 1 else beVal (tagged "KeyAgg coefficient" (hashKeys pks ++ pk)) % n

/-- `KeyAggCoeff(pk_1..pk_u, pk')`. -/
def keyAggCoeff (pks : List Bytes) (pk : Bytes) : ℕ :=
  keyAggCoeffInternal pks pk (getSecondKey pks)

/-- `Σ_i a_i ⋅ P_i` over the keys `l` (coefficients with respect to the full list `pks`);
`none` if some key fails to parse. -/
def keyAggSum (pks : List Bytes) : List Bytes → Option Point
  | [] => some none
  | pk :: rest =>
    match cpoint pk, keyAggSum pks rest with
    | some P, some acc => some (padd (pmul (keyAggCoeff pks pk) (some P)) acc)
    | _, _ => none

/-- `KeyAgg(pk_1..pk_u)`: fails if a key does not parse or the aggregate is infinity. -/
def keyAgg (pks : List Bytes) : Option KeyAggCtx :=
  match keyAggSum pks pks with
  | some (some Q) => some ⟨Q, 1, 0⟩
  | _ => none

/-- `ApplyTweak(keyagg_ctx, tweak, is_xonly_t)`. -/
def applyTweak (ctx : KeyAggCtx) (tweak : Bytes) (isXonly : Bool) : Option KeyAggCtx :=
  let g := if isXonly ∧ ¬ hasEvenY ctx.Q then n - 1 else 1
  let t := beVal tweak
  if n ≤ t then none
  else match padd (pmul g (some ctx.Q)) (pmul t G) with
    | none => none
    | some Q' => some ⟨Q', g * ctx.gacc % n, (t + g * ctx.tacc) % n⟩

/-- The tweaks of a session applied in order. -/
def applyTweaks : KeyAggCtx → List (Bytes × Bool) → Option KeyAggCtx
  | ctx, [] => some ctx
  | ctx, (tw, x) :: rest =>
    match applyTweak ctx tw x with
    | none => none
    | some ctx' => applyTweaks ctx' rest

/-- `keyagg_ctx_v`: `KeyAgg` followed by the tweaks. -/
def keyAggTweaked (pks : List Bytes) (tweaks : List (Bytes × Bool)) : Option KeyAggCtx :=
  match keyAgg pks with
  | none => none
  | some ctx => applyTweaks ctx tweaks

/-- `R_j = Σ_i R_{i,j}` for `j ∈ {0, 1}`, with `R_{i,j} = cpoint(pubnonce_i[33j : 33(j+1)])`. -/
def nonceSum (j : ℕ) : List Bytes → Option Point
  | [] => some none
  | pn :: rest =>
    match cpoint ((pn.drop (33 * j)).take 33), nonceSum j rest with
    | some P, some acc => some (padd (some P) acc)
    | _, _ => none

/-- `NonceAgg(pubnonce_1..pubnonce_u) = cbytes_ext(R_1) || cbytes_ext(R_2)`. -/
def nonceAgg (pubnonces : List Bytes) : Option Bytes :=
  match nonceSum 0 pubnonces, nonceSum 1 pubnonces with
  | some R1, some R2 => some (cbytesExt R1 ++ cbytesExt R2)
  | _, _ => none

/-- `SessionContext(aggnonce, pk_1..pk_u, tweak_1..v, is_xonly_1..v, m)`. -/
structure SessionCtx where
  aggnonce : Bytes
  pks : List Bytes
  tweaks : List (Bytes × Bool)
  msg : Bytes

/-- The values `(Q, gacc, tacc, b, R, e)` of `GetSessionValues`, together with the raw aggregate
nonce `R' = R_1 + b⋅R_2` before the infinity substitution. -/
structure SessionValues where
  Q : ℕ × ℕ
  gacc : ℕ
  tacc : ℕ
  b : ℕ
  R' : Point
  R : ℕ × ℕ
  e : ℕ

/-- `GetSessionValues(session_ctx)`. -/
def getSessionValues (ctx : SessionCtx) : Option SessionValues :=
  match keyAggTweaked ctx.pks ctx.tweaks with
  | none => none
  | some kctx =>
    let b := beVal (tagged "MuSig/noncecoef" (ctx.aggnonce ++ xbytes kctx.Q ++ ctx.msg)) % n
    match cpointExt (ctx.aggnonce.take 33), cpointExt ((ctx.aggnonce.drop 33).take 33) with
    | some R1, some R2 =>
      let R' := padd R1 (pmul b R2)
      let R := match R' with
        | none => (Gx, Gy)
        | some R => R
      let e := beVal (tagged "BIP0340/challenge" (xbytes R ++ xbytes kctx.Q ++ ctx.msg)) % n
      some ⟨kctx.Q, kctx.gacc, kctx.tacc, b, R', R, e⟩
    | _, _ => none

/-- `PartialSigVerifyInternal(psig, pubnonce, pk, session_ctx)`. -/
def partialSigVerifyInternal (psig pubnonce pk : Bytes) (ctx : SessionCtx) : Bool :=
  match getSessionValues ctx with
  | none => false
  | some sv =>
    let s := beVal psig
    if psig.length ≠ 32 ∨ n ≤ s then false
    else match cpoint (pubnonce.take 33), cpoint ((pubnonce.drop 33).take 33), cpoint pk with
      | some R1, some R2, some P =>
        if pk ∉ ctx.pks then false
        else
          let Re' := padd (some R1) (pmul sv.b (some R2))
          let Re := if hasEvenY sv.R then Re' else pneg Re'
          let a := keyAggCoeff ctx.pks pk
          let g := if hasEvenY sv.Q then 1 else n - 1
          let g' := g * sv.gacc % n
          decide (pmul s G = padd Re (pmul (sv.e * a * g' % n) (some P)))
      | _, _, _ => false

/-- `PartialSigAgg(psig_1..psig_u, session_ctx) = xbytes(R) || bytes(32, s)`. -/
def partialSigAgg (psigs : List Bytes) (ctx : SessionCtx) : Option Bytes :=
  match getSessionValues ctx with
  | none => none
  | some sv =>
    if psigs.any (fun ps => decide (ps.length ≠ 32 ∨ n ≤ beVal ps)) then none
    else
      let g := if hasEvenY sv.Q then 1 else n - 1
      let s := ((psigs.map beVal).sum + sv.e * g * sv.tacc) % n
      some (xbytes sv.R ++ BitcoinTaproot.be32 s)

/-! ### FROST-style threshold combination: Lagrange coefficients at `0` -/

/-- The Lagrange coefficient `λ_i = ∏_{j ∈ S, j ≠ i} j / (j - i)` in `ZMod n` of the participant
identifier `i`, for the signing set `S`. -/
def lagrangeCoeff (S : Finset ℕ) (i : ℕ) : ZMod n :=
  ∏ j ∈ S.erase i, (j : ZMod n) * ((j : ZMod n) - (i : ZMod n))⁻¹

end BitcoinMuSig


