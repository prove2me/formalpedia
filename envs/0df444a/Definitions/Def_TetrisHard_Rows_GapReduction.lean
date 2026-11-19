-- Prove2me | Definitions.Def_TetrisHard_Rows_GapReduction
-- name    : TetrisHard_Rows_GapReduction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-18T20:07:30.480302+00:00
-- url     : https://prove2.me/theorems/688516aa-e6ff-4af3-b486-67aa8c6dc18f
-- title:
--   Amplified reservoir game, normalized source instance and no-case bound for Theorem 6.5
-- statement:
--   Auxiliary objects for the $p^{1-\varepsilon}$ inapproximability of cleared rows (Theorem 6.5).
--
--   1. **Scaling.** For a 3-Partition instance $P=(s,T,a_1,\dots,a_{3s})$, $\mathrm{scale}(P)$ multiplies the target and every entry by $6s$. This is the normalization of Section 3: validity and the answer are preserved, the target becomes even, and every subset sum different from the target misses it by at least $6s\ge 3s$.
--   2. **Fixed instances.** $\mathrm{yes}=(1,3;1,1,1)$ is a valid yes-instance; $\mathrm{no}=(2,13;4,4,4,4,4,6)$ is a valid no-instance (every triple sums to $12$ or $14$).
--   3. **Decoding a word.** For a binary word $w$, $\mathrm{raw}(w)$ is the valid instance with at least one part coded by $w$, if there is one; the fixed yes-instance if $w$ codes a valid instance with $s=0$ (such instances are always yes-instances); and the fixed no-instance otherwise. $\mathrm{norm}(w)=\mathrm{scale}(\mathrm{raw}(w))$.
--   4. **No-case bound.** With $h_0$ the height of the base board $G(P)$ (including its staging rows) and $n_0$ the length of the base piece sequence,
--   $$a(P)=2\,(h_0+2)+4\,(n_0+1).$$
--   This number does not depend on the reservoir height $r$: $h_0+2$ is the number of rows at or above the second lock in Figure 9(b), and $4(n_0+1)$ is the area of all pieces up to and including the extra RG.
--   5. **Reservoir height.** With $M(P)=n_0+6s+7$ (so the amplified sequence has at most $M(P)\,r$ pieces for $r\ge 1$) and a fixed exponent parameter $k$,
--   $$r_k(P)=2\,\bigl(a(P)\,M(P)+1\bigr)^k,$$
--   an even number polynomial in the unary size of $P$ for fixed $k$.
--   6. **Amplified game.** $\mathrm{gapGame}_{\sigma,k}(w)$ is the reservoir game of Figure 9(b) for $\mathrm{norm}(w)$ with staging $\sigma$ and reservoir height $r_k(\mathrm{norm}(w))$.
--
--   These objects make the choice "$r>a^{2/\varepsilon}$ rows in the reservoir" of the proof of Theorem 6.5 explicit and polynomial.
--
--   **Formalization Note** The paper's no-case bound "at most $a$ rows" is replaced by the conservative cumulative bound $a(P)$ above, which accounts separately for rows cleared before and during the final square sequence; the final exponent is unaffected.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (normalization, p. 7), Section 6.2 and Figure 9(b) (pp. 19-21), proof of Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

/-- Multiply every entry and the target by `6s`. This preserves validity and the answer,
and makes the target even with all subset-sum gaps multiples of `6s` (Section 3). -/
def ThreePartition.scale (P : ThreePartition) : ThreePartition where
  s := P.s
  target := 6 * P.s * P.target
  entry := fun i => 6 * P.s * P.entry i

/-- A fixed valid "yes" instance with one part: `1+1+1 = 3`. -/
def yesInstance : ThreePartition := ⟨1, 3, fun _ => 1⟩

/-- A fixed valid "no" instance with two parts: entries `4,4,4,4,4,6`, target `13`;
every triple sums to `12` or `14`. -/
def noInstance : ThreePartition := ⟨2, 13, ![4, 4, 4, 4, 4, 6]⟩

/-- Decode a binary word as a source instance. Codes of valid instances with at least one
part decode to that instance; codes of valid empty instances (always "yes") decode to the
fixed yes instance; every other word decodes to the fixed no instance. -/
noncomputable def rawInstance (w : List Bool) : ThreePartition := by
  classical
  exact if h : ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code then Classical.choose h
    else if ∃ P : ThreePartition, P.Valid ∧ w = P.code then yesInstance else noInstance

/-- The normalized source instance attached to a binary word. -/
noncomputable def normInstance (w : List Bool) : ThreePartition := (rawInstance w).scale

/-- Polynomial bound on the cumulative number of rows cleared in a "no" instance:
twice the number of rows at or above the second lock, plus the area of all pieces
before the appended squares. It does not depend on the reservoir height. -/
def noBound (P : ThreePartition) (staging : ℕ) : ℕ :=
  2 * ((baseBoard P staging).height + 2) + 4 * ((basePieces P).length + 1)

/-- A factor with `|pieces| ≤ pieceFactor P * r` for every positive reservoir height `r`. -/
def pieceFactor (P : ThreePartition) : ℕ := (basePieces P).length + 6 * P.s + 7

/-- The explicit (even) reservoir height for the exponent parameter `k`. -/
def gapRows (P : ThreePartition) (staging k : ℕ) : ℕ :=
  2 * (noBound P staging * pieceFactor P + 1) ^ k

/-- The amplified Tetris game attached to a binary word. -/
noncomputable def gapGame (staging k : ℕ) (w : List Bool) : Game :=
  reservoirGame (normInstance w) staging (gapRows (normInstance w) staging k)

end TetrisHard.Rows


