-- Prove2me | Definitions.Def_ExactPatternStream_SeededHash
-- name    : ExactPatternStream_SeededHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:27.225217+00:00
-- url     : https://prove2.me/theorems/b10e814d-93e5-4b62-baf1-0f78e3aef22b
-- title:
--   (14), §7.4 — $\mathcal L$, $b$, $k_{\mathrm{cnt}}$, codes, keys, $F_i$, seeds, $f_R$
-- statement:
--   The parameters are $\mathcal L=8\lceil\log_2(m+|\Sigma|)\rceil$, $b=16\lceil\log_2\mathcal L\rceil$, $k_{\mathrm{cnt}}=\lceil\log_2(4\mathcal L)\rceil$, $b_0=\lceil\log_2(|\Sigma|+2)\rceil$, $b_i=2+b+b_{\mathrm{cnt}}$. The codes are $\mathrm{code}_i((y,z,\alpha))=0\circ y\circ\mathrm{code}_{\mathrm{cnt}}(z)\circ\alpha$ and $\mathrm{code}_i(\#_i)=1\circ0^{b+b_{\mathrm{cnt}}+1}$, and $\mathrm{key}_i$ concatenates the codes of a group, of length $L_i=(c_i+2)b_i$.
--
--   For a group $G=(x_0,\dots,x_{c_i+1})$,
--   $$F_i(G)=\big(H_i(\mathrm{key}_i(G)),\ \mathrm{Sum}_{k_{\mathrm{cnt}}}(\mathrm{cnt}_i(x_0),\dots,\mathrm{cnt}_i(x_{c_i+1})),\ \alpha_i(G)\big),$$
--   with $H_i\in\mathcal H_{L_i,b}$, $\mathrm{cnt}_i$ as on p.21, and $\alpha_i(G)=1$ iff $x_{c_i+1}=\#_i$ or both $x_1\cdots x_{c_i+1}=u_i^{c_i}\circ v_i$ and $\alpha(x_0)=1$.
--
--   §7.4: over $\mathbb F_{p_R}$, $\#\mapsto0$, $\Sigma$ injects into the nonzero elements, and $f_R(Y)=\big(|Y|,\sum_{u<|Y|}Y[u]a_R^{|Y|-1-u}\big)$.
--
--   **Formalization Note** The paper's "any injective" codes are fixed: $a\mapsto a$, $\$\mapsto\sigma$, $\#_0\mapsto\sigma+1$ in $b_0$ bits at level $0$; $M$ in $k_{\mathrm{cnt}}+1$ bits and $s$ in $\lceil\log_2(\mathcal L+1)\rceil$ bits for a counter. In $f_R$, $a\mapsto a+1$. The seeds `Seeds σ m` have one independent uniform block per level, of which level $i$ reads the prefix its $H_i$ needs. So they have the law of sampling $H_i$ once $P_i$ is known, even though $L_i$ depends on the lower levels. Blocks of `blockLen σ m` pairs suffice: $h\le m$, $c_i\le m$, $D\le d\le L_i$. `answersOf` is the reporting rule of §9.4.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §7.3–§7.4, pp.20–22 (PDF 21–23), eq. (14), (16); §9.4, p.29 (PDF 30)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily
import Definitions.Def_ExactPatternStream_Counters

namespace ExactPatternStream

/-! # The functions `F_i` of (14) and `f_R`

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §7.3–§7.4, pp.20–22 (PDF 21–23),
eq. (14), eq. (16).

**Formalization Note.** `bigL σ m` is the paper's calligraphic `𝓛 = 8⌈log₂(m + |Σ|)⌉` (not the `L` of
Lemma 7.4). The paper's "any injective code" `code_0` is the binary code `a ↦ a`, `$ ↦ σ`, `#₀ ↦ σ + 1`; its
"fixed-width injective encoding" of a counter is `M` in `k_cnt + 1` bits and `s` in `⌈log₂(𝓛+1)⌉` bits, which
holds every represented count (`< 2^𝓛`, p.20). Labels outside the level's alphabet have the all-zero code;
they do not occur. The seeds: decision 8 of the plan. `Seeds σ m` has one independent uniform block per
level, and level `i` reads the prefix `H_{L_i,b}` needs. `L_i` depends on `c_i`, hence on the lower levels'
hashes, but the block of level `i` is independent of them, so this has the law of sampling `H_i` once `P_i`
is known. `(m + 2)` blocks of `blockLen σ m` pairs always suffice: `h ≤ m`, `c_i ≤ m`, and `D ≤ d ≤ L_i`.
`f_R` maps `#` to `0` and `a ∈ Σ` to `a + 1`, which is an injection into `F_{p_R} ∖ {0}` since `p_R > σ`. -/

/-- The calligraphic `𝓛 = 8⌈log₂(m + |Σ|)⌉`, p.20. -/
def bigL (σ m : ℕ) : ℕ := 8 * Nat.clog 2 (m + σ)

/-- `b = 16⌈log₂ 𝓛⌉`, p.20. -/
def hashB (σ m : ℕ) : ℕ := 16 * Nat.clog 2 (bigL σ m)

/-- `k_cnt = ⌈log₂(4𝓛)⌉`, p.20. -/
def kCnt (σ m : ℕ) : ℕ := Nat.clog 2 (4 * bigL σ m)

/-- The bits of a counter's exponent. -/
def expBits (σ m : ℕ) : ℕ := Nat.clog 2 (bigL σ m + 1)

/-- `b_cnt = O(log 𝓛)`, p.20. -/
def bCnt (σ m : ℕ) : ℕ := kCnt σ m + 1 + expBits σ m

/-- `code_cnt`, the fixed-width encoding of a counter. -/
def codeCnt (σ m : ℕ) (z : ℕ × ℕ) : List Bool :=
  natBits (kCnt σ m + 1) z.1 ++ natBits (expBits σ m) z.2

/-- `b_0 = ⌈log₂(|Σ| + 2)⌉` and `b_i = 2 + b + b_cnt` for `i ≥ 1`, p.20. -/
def levelBits (σ m i : ℕ) : ℕ :=
  if i = 0 then Nat.clog 2 (σ + 2) else 2 + hashB σ m + bCnt σ m

/-- `code_0` and `code_i`, p.20: `code_i((y, z, α)) = 0 ◦ y ◦ code_cnt(z) ◦ α`,
`code_i(#ᵢ) = 1 ◦ 0^{b + b_cnt + 1}`. -/
def codeLabel (σ m i : ℕ) (l : Label) : List Bool :=
  if i = 0 then
    match l with
    | Label.raw a => natBits (levelBits σ m 0) a
    | Label.guard => natBits (levelBits σ m 0) σ
    | Label.marker _ => natBits (levelBits σ m 0) (σ + 1)
    | Label.node _ _ _ => List.replicate (levelBits σ m 0) false
  else
    match l with
    | Label.node y z a => false :: (y ++ codeCnt σ m z ++ [a])
    | Label.marker _ => true :: List.replicate (hashB σ m + bCnt σ m + 1) false
    | _ => List.replicate (levelBits σ m i) false

/-- `key_i(G) = code_i(x_0) ◦ ⋯ ◦ code_i(x_{c_i+1})`, p.21. -/
def keyOf (σ m i : ℕ) (g : List Label) : List Bool := g.flatMap (codeLabel σ m i)

/-- `cnt_i`, p.21: `round(1)` on `Σ`, `round(0)` on `$` and `#ᵢ`, and `z` on `(y, z, α)`. -/
def cntOf (σ m : ℕ) : Label → ℕ × ℕ
  | Label.raw _ => roundK (kCnt σ m) 1
  | Label.guard => roundK (kCnt σ m) 0
  | Label.marker _ => roundK (kCnt σ m) 0
  | Label.node _ z _ => z

/-- `α(x)`, p.21: `1` at level zero unless `x = #₀`, `α(#ᵢ) = 0`, `α((y, z, α')) = α'`. -/
def alphaOf : Label → Bool
  | Label.raw _ => true
  | Label.guard => true
  | Label.marker _ => false
  | Label.node _ _ a => a

/-- `α_i(G) = 1 ⟺ x_{c_i+1} = #ᵢ ∨ (x_1 ⋯ x_{c_i+1} = u_i^{c_i} ◦ v_i ∧ α(x_0) = 1)`, p.21. -/
def alphaGroup (i : ℕ) (u v : Label) (c : ℕ) (g : List Label) : Bool :=
  decide (g.getD (c + 1) default = Label.marker i) ||
    (decide (g.drop 1 = List.replicate c u ++ [v]) && alphaOf (g.getD 0 default))

/-- The length of one block of field-element pairs. -/
def blockLen (σ m : ℕ) : ℕ := (m + 3) * (Nat.clog 2 (σ + 2) + hashB σ m + bCnt σ m + 2)

/-- The recursive seeds: `m + 2` independent blocks of pairs in `F_p²`, `p = hashPrime b`. -/
abbrev Seeds (σ m : ℕ) :=
  Fin (m + 2) → Fin (blockLen σ m) → ZMod (hashPrime (hashB σ m)) × ZMod (hashPrime (hashB σ m))

open Classical in
/-- The seed of `H_i ∈ H_{L,b}`: the prefix of the block of level `i`. -/
noncomputable def levelSeed {σ m : ℕ} (ω : Seeds σ m) (i L : ℕ) : HSeed L (hashB σ m) := fun r =>
  if h : i < m + 2 ∧ r.val < blockLen σ m then ω ⟨i, h.1⟩ ⟨r.val, h.2⟩ else 0

/-- `F_i` of (14) at seeds `ω`: `L_i = (c_i + 2) b_i`, and
`F_i(G) = (H_i(key_i(G)), Sum_{k_cnt}(cnt_i(x_0), …, cnt_i(x_{c_i+1})), α_i(G))`. -/
noncomputable def seededF {σ m : ℕ} (ω : Seeds σ m) : GroupHash := fun i u v c g =>
  (hashEval ((c + 2) * levelBits σ m i) (hashB σ m)
      (levelSeed ω i ((c + 2) * levelBits σ m i)) (keyOf σ m i g),
    sumK (kCnt σ m) (g.map (cntOf σ m)),
    alphaGroup i u v c g)

/-- The characters of `P` or `T` as natural numbers. -/
def rawStr {σ : ℕ} (S : List (Fin σ)) : List ℕ := S.map Fin.val

/-- `Build(P, T)` at seeds `ω`, with `m = |P|`. -/
noncomputable def seededBuild {σ : ℕ} (P T : List (Fin σ)) (ω : Seeds σ P.length) : List Level :=
  build (seededF ω) (rawStr P) (rawStr T)

/-- The map of §7.4 into `F_{p_R}`: `a ↦ a + 1` on `Σ`, `# ↦ 0`. The guard never reaches `f_R`. -/
def fpEnc (pR : ℕ) : Leaf → ZMod pR
  | Leaf.sym a => ((a + 1 : ℕ) : ZMod pR)
  | _ => 0

/-- `f_R(Y) = (|Y|, Σ_{u<|Y|} Y[u] a_R^{|Y|-1-u})`, §7.4, p.22. -/
def fR {pR : ℕ} (aR : ZMod pR) (Y : List Leaf) : ℕ × ZMod pR :=
  (Y.length, ((List.range Y.length).map fun u =>
    fpEnc pR (Y.getD u Leaf.hash) * aR ^ (Y.length - 1 - u)).sum)

/-- `Match(P, T)`, Algorithm 2, at recursive seeds `ω` and the parameter `a_R` of `f_R`. -/
noncomputable def seededMatch {σ pR : ℕ} (P T : List (Fin σ)) (s : Seeds σ P.length × ZMod pR) :
    Finset ℤ :=
  matchSet (seededF s.1) (fR s.2) (rawStr P) (rawStr T)

/-- The reporting rule of §9.4, p.29: for `m ≤ t ≤ n`, YES (`1`) at raw position `t - 1` when `t - m` belongs
to the set `M`, and NO (`0`) otherwise. -/
def answersOf {σ : ℕ} (P T : List (Fin σ)) (M : Finset ℤ) : List ℕ :=
  (List.range (T.length + 1 - P.length)).map fun a => if (a : ℤ) ∈ M then 1 else 0

instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- `Occ(P, T)` as a set of integers, to compare with `M`. -/
def occZ {σ : ℕ} (P T : List (Fin σ)) : Finset ℤ := (occ P T).image fun a : ℕ => (a : ℤ)

end ExactPatternStream


