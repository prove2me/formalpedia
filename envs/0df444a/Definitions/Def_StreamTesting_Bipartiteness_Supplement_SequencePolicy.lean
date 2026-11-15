-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequencePolicy
-- name    : StreamTesting_Bipartiteness_Supplement_SequencePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:57:54.219362+00:00
-- url     : https://prove2.me/theorems/28a3eb67-051a-490b-8827-d54fb31dfd5d
-- title:
--   Forward-only real-valued sequence policies
-- statement:
--   An observed sequence history has a slot for each index: absent before arrival, a skip marker after skipping, or the actual real answer after querying. A deterministic policy chooses query or skip from the prior observed history and the current index, and computes its final output from the completed history.
--
--   $$A=(\mathrm{query}:\mathrm{History}\times[m]\to\{0,1\},\ \mathrm{output}:\mathrm{History}\to\alpha).$$
--
--   A randomized algorithm chooses a seed from an input-independent probability mass function on an arbitrary finite seed space, then uses the corresponding policy. The seed size is unrestricted. Histories and policy spaces for real values are infinite. The paper's existence algorithms use finitely many sampling choices at each fixed length, so finite seeds suffice. No restriction is placed on real values, memory, computation, or history dependence. Outputs may be Boolean decisions or optional real search values.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed/PDF p.3; sequence setting p.5; §§5–6, printed/PDF pp.26–36.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

/-- Outer none: not elapsed; some none: skipped; some (some x): actual queried value.
The slot identifies the elapsed index. The real-history space is not finite. -/
abbrev SeqHistory (m : ℕ) := Fin m → Option (Option ℝ)

abbrev SeqPolicy (m : ℕ) (α : Type) :=
  (SeqHistory m → Fin m → Bool) × (SeqHistory m → α)

/-- A finite private seed space, of unrestricted size, sufficient for the existence bounds.
Only the seed space is finite; decisions can depend on arbitrary observed real values. -/
structure SeqAlgorithm (m : ℕ) (α : Type) where
  seedCount : ℕ
  coins : PMF (Fin seedCount)
  policy : Fin seedCount → SeqPolicy m α

end StreamTesting.Bipartiteness.Supplement


