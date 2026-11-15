-- Prove2me | Definitions.Def_InfoLossLAR_NativeSupplement_01
-- name    : InfoLossLAR_NativeSupplement_01
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T20:35:53.205943+00:00
-- url     : https://prove2.me/theorems/239a9f37-da00-4b1b-a61b-318c7529b02f
-- title:
--   Exact native arithmetic and materialization interfaces
-- statement:
--   This package supplies the native arithmetic, finite-coordinate, and materialization interfaces used to compile the affine transport sampler. It includes compatible-fiber operations, bounds for integer linear iteration, and binary root metadata. Supporting identities identify the decoded rational or integer output with its mathematical value. These identities are proved here and are used to construct the numerical data; they do not assume a transport theorem or a worst-case lattice reduction.
-- source:
--   Companion Lean implementation for the fixed-family Gaussian affine transport theorem. The source modules and their SHA-256 hashes are recorded in the checked extraction manifest. This exact generated file has SHA-256 abc9cbcc0183eb700f512bd5cf3c5a277249237e6010557b5f45b2744196dd07. Native mathematical source originates from manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; compatibility changes are checked against the target Lean environment. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 425659ebbde85bbbf5837e8074c66807a9eaaa4fde9c14c3a963078c64999c2a. Native10/11 split fallback keeps every original scope-closed data body unchanged and retains the canonical module names as import facades. Current source SHA256 425659ebbde85bbbf5837e8074c66807a9eaaa4fde9c14c3a963078c64999c2a.

-- Source module: AFT.GaussianSource











import Definitions.Def_InfoLossLAR_NativeBundle_12
















































namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryFiniteProduct
end CurrentAFT.BinaryFiniteProduct
namespace CurrentAFT.BinaryFullResponseCounts
end CurrentAFT.BinaryFullResponseCounts
namespace CurrentAFT.BinaryListSum
end CurrentAFT.BinaryListSum
namespace CurrentAFT.BinaryRootMetadataSerializer
end CurrentAFT.BinaryRootMetadataSerializer
namespace CurrentAFT.BinarySparseCycleEvaluation
end CurrentAFT.BinarySparseCycleEvaluation
namespace CurrentAFT.BinarySparseCycleSemantic
end CurrentAFT.BinarySparseCycleSemantic
namespace CurrentAFT.BinaryTouchedCycle
end CurrentAFT.BinaryTouchedCycle
namespace CurrentAFT.BinaryTouchedCycleBuffer
end CurrentAFT.BinaryTouchedCycleBuffer
namespace CurrentAFT.BinaryTouchedCycleRanks
end CurrentAFT.BinaryTouchedCycleRanks
namespace CurrentAFT.BinaryTupleSum
end CurrentAFT.BinaryTupleSum
namespace CurrentAFT.CountedBoundedRootTags
end CurrentAFT.CountedBoundedRootTags
namespace CurrentAFT.CountedBoundedRootTags.Tag
end CurrentAFT.CountedBoundedRootTags.Tag
namespace CurrentAFT.CurrentCycleEntryProgram
end CurrentAFT.CurrentCycleEntryProgram
namespace CurrentAFT.CurrentGaussianBits
end CurrentAFT.CurrentGaussianBits
namespace CurrentAFT.CurrentPublicShiftProgram
end CurrentAFT.CurrentPublicShiftProgram
namespace CurrentAFT.CurrentRootSlotIndex
end CurrentAFT.CurrentRootSlotIndex
namespace CurrentAFT.CyclePatternProgram
end CurrentAFT.CyclePatternProgram
namespace CurrentAFT.CycleRootExpansion
end CurrentAFT.CycleRootExpansion
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.FullResponseEnumeration
end CurrentAFT.FullResponseEnumeration
namespace CurrentAFT.JointTaggedPhysicalFock
end CurrentAFT.JointTaggedPhysicalFock
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.ProtectedCycle
end CurrentAFT.ProtectedCycle
namespace CurrentAFT.RationalScalarFamilyAverage
end CurrentAFT.RationalScalarFamilyAverage
namespace CurrentAFT.RootSignedMassProgram
end CurrentAFT.RootSignedMassProgram
namespace CurrentAFT.TensorPublicProjection
end CurrentAFT.TensorPublicProjection
namespace InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation
end InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation
namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic
end InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic
namespace InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic
end InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic
namespace InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram
end InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram
namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage
end InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage
namespace InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion
end InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion
namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation
end InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation
namespace InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex
end InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex
namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram
end InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram
namespace InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram
end InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram
namespace InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum
end InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum
namespace InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters
end InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters
namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments
end InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments
namespace InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle
end InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle
namespace InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram
end InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram
namespace InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections
end InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections
namespace InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag
end InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag
namespace InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle
end InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle
namespace InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle
end InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle
namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits
namespace InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram
end InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram
namespace InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer
end InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer
namespace InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag
end InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag
namespace InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration
end InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration
namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram
end InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram
namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle
end InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle
namespace InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag
end InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag
namespace InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram
end InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram
namespace InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle
end InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle
namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum
end InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum
namespace InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum
end InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum
namespace InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum
end InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum
namespace InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics
end InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic
end InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic
namespace InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration
end InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration
namespace InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic
end InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic
namespace InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration
end InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration
namespace InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection
end InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection
namespace InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic
namespace InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle
end InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle
namespace InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum
end InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum
namespace InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram
end InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram
namespace InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag
end InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag
namespace InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation
end InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation
namespace InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections
end InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections
namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation
end InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation
namespace InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct
end InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct
namespace InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags
end InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags
namespace InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock
end InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock
namespace InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound
namespace InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts
end InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts
namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics
namespace InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks
end InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks
namespace InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation
end InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation
namespace InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag
end InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag
namespace InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer
end InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer
namespace InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits
end InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits
namespace InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments
end InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments
section


/-!
# A genuine discrete Gaussian source and its full-support residue law

The one-dimensional Gaussian is normalized on the infinite integer lattice.
Its summability is proved by comparison with a geometric exponential series,
not assumed. Independent coordinate products give the source on `ℤ^d`.
Reduction modulo a positive modulus has full support, closing the analytic
source premise in the finite full-support obstruction.
-/

namespace AFT
namespace GaussianSource

open scoped BigOperators Classical ENNReal



















set_option maxRecDepth 8192
/-- Independent coordinate products on integer vectors. -/
noncomputable def _root_.AFT.GaussianSource.independentCoordinates (p : PMF ℤ) :
    (dimension : ℕ) → PMF (Fin dimension → ℤ)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | dimension + 1 => p.bind (fun head =>
      (independentCoordinates p dimension).map (Fin.cons head))





set_option maxRecDepth 8192
/-- The isotropic discrete Gaussian on the integer coordinate lattice. -/
noncomputable def _root_.AFT.GaussianSource.latticeGaussian (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    PMF (Fin dimension → ℤ) :=
  independentCoordinates (integerGaussian width hwidth) dimension



set_option maxRecDepth 8192
/-- Unnormalized multivariate Gaussian weight. -/
noncomputable def _root_.AFT.GaussianSource.latticeWeight (dimension : ℕ) (width : ℝ)
    (vector : Fin dimension → ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ∑ coordinate, (vector coordinate : ℝ) ^ 2)







set_option maxRecDepth 8192
/-- Convert a finite PMF to the real-weight interface used by the AFT proofs. -/
noncomputable def _root_.AFT.GaussianSource.finiteLaw {α : Type*} [Fintype α] (p : PMF α) : FiniteDist α where
  weight a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := by
    rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
    have hsum : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [hsum, ENNReal.toReal_one]



set_option maxRecDepth 8192
/-- Coordinatewise residue reduction of a genuine lattice Gaussian. -/
noncomputable def _root_.AFT.GaussianSource.residueGaussian (dimension modulus : ℕ) [NeZero modulus]
    (width : ℝ) (hwidth : 0 < width) : FiniteDist (Fin dimension → ZMod modulus) :=
  finiteLaw ((latticeGaussian dimension width hwidth).map
    (fun vector coordinate => (vector coordinate : ZMod modulus)))







end GaussianSource
end AFT

end


-- Source module: AFT.ActualPublicSources
section



/-! # Actual public choices have disjoint, queue-free physical root sources -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]






























set_option maxRecDepth 8192
/-- Canonical finite numberings turn any legal distinct pool indices into
actual public choices; no matching or source-disjointness hypothesis is used. -/
def _root_.AFT.V7Calibration.actualPublicPrimaryFromIndices (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (indices : Primary ↪ Fin (actualControlPool n placement).card) : ActualPublicPrimaryChoice n placement Primary :=
  indices.trans (finiteSetNumbering (blockIndexNumbering n) (actualControlPool n placement)).toEmbedding

set_option maxRecDepth 8192
def _root_.AFT.V7Calibration.actualPublicBodyFromIndices (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (indices : Body ↪ Fin (actualReservedBodies n placement).card) : ActualPublicBodyChoice n placement Body :=
  indices.trans (finiteSetNumbering (blockIndexNumbering n) (actualReservedBodies n placement)).toEmbedding

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration.actualPublicPrimaryChoice_nonempty (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (hsize : Fintype.card Primary≤(actualControlPool n placement).card) :
    Nonempty (ActualPublicPrimaryChoice n placement Primary) := by
  exact ⟨actualPublicPrimaryFromIndices n placement ((Fintype.equivFin Primary).toEmbedding.trans (Fin.castLEEmb hsize))⟩
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → AFT.V7Calibration.actualPublicPrimaryChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → _p2mNS29


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration.actualPublicBodyChoice_nonempty (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (hsize : Fintype.card Body≤(actualReservedBodies n placement).card) :
    Nonempty (ActualPublicBodyChoice n placement Body) := by
  exact ⟨actualPublicBodyFromIndices n placement ((Fintype.equivFin Body).toEmbedding.trans (Fin.castLEEmb hsize))⟩
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → AFT.V7Calibration.actualPublicBodyChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → _p2mNS28


end
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → AFT.V7Calibration.actualPublicBodyChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → _p2mNS28
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → AFT.V7Calibration.actualPublicPrimaryChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → _p2mNS29

end AFT.V7Calibration
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → AFT.V7Calibration.actualPublicBodyChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → _p2mNS28
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → AFT.V7Calibration.actualPublicPrimaryChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → _p2mNS29


end
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → AFT.V7Calibration.actualPublicBodyChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → _p2mNS28
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → AFT.V7Calibration.actualPublicPrimaryChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → _p2mNS29


-- Source module: AFT.RationalHeight
section


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
open scoped BigOperators



namespace HeightBound

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound.mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → _p2mNS6


set_option maxRecDepth 8192
 theorem _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound.reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → AFT.RationalNumerics.HeightBound.reduced_le
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → _p2mNS135



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound.one : HeightBound 1 0 := by norm_num [HeightBound]
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → _p2mNS10


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound.of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → AFT.RationalNumerics.HeightBound.of_int
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → _p2mNS8


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound.of_nat {value bits : ℕ} (h : value ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  simpa only [Int.cast_natCast] using _p2mNS8 (value:=(value : ℤ)) (by simpa using h)
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → AFT.RationalNumerics.HeightBound.of_nat
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → _p2mNS9








set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound.mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := _p2mNS135 (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → _p2mNS7


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound.inv {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by
  by_cases hz : value=0
  · subst value
    norm_num [HeightBound]
    exact Nat.one_le_pow bits 2 (by decide)
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hsign : value.num.sign.natAbs=1 := by
      rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hz) with hn|hn
      · simp [Int.sign_eq_neg_one_of_neg hn]
      · simp [Int.sign_eq_one_of_pos hn]
    simpa only [hsign,one_mul,mul_one] using h.2
  · simpa only [Rat.den_inv_of_ne_zero hz] using h.1
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → AFT.RationalNumerics.HeightBound.inv
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → _p2mNS5


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound.div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → AFT.RationalNumerics.HeightBound.div
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → _p2mNS4


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound.pow {value : ℚ} {bits : ℕ} (h : HeightBound value bits) (power : ℕ) :
    HeightBound (value^power) (bits*power) := by
  induction power with
  | zero => simpa using _p2mNS10
  | succ power ih => simpa only [pow_succ,Nat.mul_succ] using ih.mul h
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → AFT.RationalNumerics.HeightBound.pow
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → _p2mNS11






end HeightBound
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → AFT.RationalNumerics.HeightBound.div
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → _p2mNS4
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → AFT.RationalNumerics.HeightBound.inv
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → _p2mNS5
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → _p2mNS6
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → _p2mNS7
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → AFT.RationalNumerics.HeightBound.of_int
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → _p2mNS8
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → AFT.RationalNumerics.HeightBound.of_nat
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → _p2mNS9
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → _p2mNS10
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → AFT.RationalNumerics.HeightBound.pow
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → _p2mNS11
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → AFT.RationalNumerics.HeightBound.reduced_le
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → _p2mNS135

end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → AFT.RationalNumerics.HeightBound.div
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → _p2mNS4
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → AFT.RationalNumerics.HeightBound.inv
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → _p2mNS5
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → _p2mNS6
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → _p2mNS7
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → AFT.RationalNumerics.HeightBound.of_int
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → _p2mNS8
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → AFT.RationalNumerics.HeightBound.of_nat
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → _p2mNS9
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → _p2mNS10
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → AFT.RationalNumerics.HeightBound.pow
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → _p2mNS11
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → AFT.RationalNumerics.HeightBound.reduced_le
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → _p2mNS135


end
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → AFT.RationalNumerics.HeightBound.inv
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → _p2mNS5
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → AFT.RationalNumerics.HeightBound.div
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → _p2mNS4
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → _p2mNS7
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → _p2mNS10
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → _p2mNS6
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → AFT.RationalNumerics.HeightBound.of_nat
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → _p2mNS9
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → AFT.RationalNumerics.HeightBound.pow
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → _p2mNS11
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → AFT.RationalNumerics.HeightBound.of_int
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → _p2mNS8


-- Source module: AFT.BinaryRationalLiterals
section


/-! Finite stored literals and explicit copying. `exists_code` is a semantic
encoding theorem; it is not a runtime rational-to-bits oracle. Programs store
its finite Boolean literals before execution. -/
namespace AFT.BinaryArithmetic







set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic.bits_value (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec with
  | zero => simp [value]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit_val,value]
    · rw [Nat.bits_append_bit n b (fun hh => False.elim (hn hh))]
      simp only [value,ih,Nat.bit_val]
      omega
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → AFT.BinaryArithmetic.bits_value
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → _p2mNS1


namespace RationalBits







set_option maxRecDepth 8192
/-- Existence of a finite literal encoding, used when constructing a fixed
program. The result is stored data, not an invocation of a real oracle. -/
theorem _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits.exists_code (q : ℚ) : ∃ code : RationalBits,code.decode=q := by
  let negative := decide (q.num < 0)
  have hsign : signedValue negative q.num.natAbs.bits=q.num := by
    simp only [signedValue,_p2mNS1,negative]
    by_cases hn : q.num < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (by omega : 0 ≤ q.num)]
  let code : RationalBits :=
    ⟨negative,q.num.natAbs.bits,q.den.bits,
      by rw [_p2mNS1,Nat.size_eq_bits_len],
      by rw [_p2mNS1,Nat.size_eq_bits_len],
      by simpa only [_p2mNS1] using q.den_pos,
      by simpa only [_p2mNS1] using q.reduced⟩
  refine ⟨code,?_⟩
  rw [decode_fraction]
  change (signedValue negative q.num.natAbs.bits : ℚ)/(value q.den.bits : ℚ)=q
  rw [hsign,_p2mNS1,Rat.num_div_den]
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → _p2mNS0


end RationalBits
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → _p2mNS0

end AFT.BinaryArithmetic
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → _p2mNS0
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → AFT.BinaryArithmetic.bits_value
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → _p2mNS1


end
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → _p2mNS0
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → AFT.BinaryArithmetic.bits_value
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → _p2mNS1


-- Source module: AFT.CompatibleFibers
section


/-! # Mixed fibers for unequal pools with their actual separate reference laws -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

set_option maxRecDepth 8192
/-- Reindexing a nonidentical product law transports every coordinate law. -/
theorem _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments.independent_equiv_expectation_general (equiv : Slot ≃ Pool)
    (reference : Pool → FiniteDist Color) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun slot => reference (equiv slot))).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, (reference (equiv slot)).weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, (reference slot).weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, (reference (equiv slot)).weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => (reference slot).weight (word slot))).symm
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → AFT.CanonicalMoments.independent_equiv_expectation_general
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → _p2mNS3


set_option maxRecDepth 8192
/-- The exact law of an arbitrary injective subword of nonidentical inputs. -/
theorem _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments.independent_embedding_expectation_general (reference : Pool → FiniteDist Color)
    (placement : Slot ↪ Pool) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun slot => reference (placement slot))).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation reference (Finset.univ.map placement)
    (fun word => function (word ∘ placementEquiv placement))
  have he := _p2mNS3 (placementEquiv placement)
    (fun label : Finset.univ.map placement => reference label) function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → AFT.CanonicalMoments.independent_embedding_expectation_general
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → _p2mNS2








end AFT.CanonicalMoments
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → AFT.CanonicalMoments.independent_embedding_expectation_general
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → _p2mNS2
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → AFT.CanonicalMoments.independent_equiv_expectation_general
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → _p2mNS3


end
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → AFT.CanonicalMoments.independent_equiv_expectation_general
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → _p2mNS3
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → AFT.CanonicalMoments.independent_embedding_expectation_general
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → _p2mNS2


-- Source module: AFT.CountedRootSelections
section





/-! # Fixed-order root-set enumeration, without an exponential powerset

The include/exclude recursion stops as soon as the requested cardinality
is zero. Its stored work and output lengths have polynomial bounds for
fixed order. The actual response uses orders at most twice its cutoff.
-/
namespace AFT.RationalNumerics
open scoped BigOperators















set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics.mem_boundedRootList (population bound : ℕ) (selected : Finset (Fin population)) :
    selected∈boundedRootList population bound ↔ selected.card≤bound := by
  simp only [boundedRootList,List.mem_flatMap,List.mem_range,List.mem_map,countedSubsequences_value]
  constructor
  · rintro ⟨order,horder,word,hword,rfl⟩
    obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hword
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange population)),hlen]
    omega
  · intro hcard
    let word := (List.finRange population).filter (fun point => decide (point∈selected))
    have hset : word.toFinset=selected := by
      ext point
      simp [word]
    have hlen : word.length=selected.card := by
      rw [←hset,List.toFinset_card_of_nodup]
      exact List.Nodup.filter _ (List.nodup_finRange population)
    refine ⟨selected.card,by omega,word,List.mem_sublistsLen.mpr ⟨List.filter_sublist,hlen⟩,hset⟩
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → AFT.RationalNumerics.mem_boundedRootList
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → _p2mNS25








set_option maxRecDepth 8192
/-- The ordered sublists already distinguish the root sets. No duplicate
removal is needed by a summation evaluator. -/
theorem _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics.boundedRootList_nodup (population bound : ℕ) :
    (boundedRootList population bound).Nodup := by
  unfold boundedRootList
  simp only [countedSubsequences_value]
  apply List.nodup_flatMap.mpr
  constructor
  · intro order _
    apply List.Nodup.map_on _ (List.nodup_sublistsLen order (List.nodup_finRange population))
    intro first hf second hs he
    have hf' := (List.mem_sublistsLen.mp hf).1
    have hs' := (List.mem_sublistsLen.mp hs).1
    have hm : ∀ point,point∈first ↔ point∈second := by
      intro point
      simpa only [List.mem_toFinset] using (Iff.of_eq (congrArg (fun s : Finset (Fin population) => point∈s) he))
    exact List.Subset.antisymm_of_pairwise
      ((List.sortedLT_finRange population).pairwise.sublist hf')
      ((List.sortedLT_finRange population).pairwise.sublist hs')
      (fun point hp => (hm point).mp hp) (fun point hp => (hm point).mpr hp)
  · apply (List.nodup_range (n := bound+1)).imp
    intro first second hne selected hf hs
    obtain ⟨left,hl,rfl⟩ := List.mem_map.mp hf
    obtain ⟨right,hr,he⟩ := List.mem_map.mp hs
    have hl' := List.mem_sublistsLen.mp hl
    have hr' := List.mem_sublistsLen.mp hr
    have hc := congrArg Finset.card he
    rw [List.toFinset_card_of_nodup (hr'.1.nodup (List.nodup_finRange population)),
      List.toFinset_card_of_nodup (hl'.1.nodup (List.nodup_finRange population)),hr'.2,hl'.2] at hc
    exact hne hc.symm
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → AFT.RationalNumerics.boundedRootList_nodup
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → _p2mNS14














end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → AFT.RationalNumerics.boundedRootList_nodup
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → _p2mNS14
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → AFT.RationalNumerics.mem_boundedRootList
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → _p2mNS25


end
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → AFT.RationalNumerics.mem_boundedRootList
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → _p2mNS25
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → AFT.RationalNumerics.boundedRootList_nodup
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → _p2mNS14


-- Source module: AFT.RationalCommonDenominator
section


/-! # A computed common denominator with polynomial binary height -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Index : Type*} [Fintype Index]





set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics.commonDenominator_pos (values : Index → ℚ) : 0<commonDenominator values :=
  Finset.prod_pos (fun index _ => (values index).den_pos)
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → AFT.RationalNumerics.commonDenominator_pos
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → _p2mNS16


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics.denominator_dvd_common (values : Index → ℚ) (index : Index) :
    (values index).den∣commonDenominator values :=
  Finset.dvd_prod_of_mem (fun index => (values index).den) (Finset.mem_univ index)
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → AFT.RationalNumerics.denominator_dvd_common
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → _p2mNS20


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics.commonNumerator_cast (values : Index → ℚ) (index : Index) :
    (commonNumerator values index : ℚ)=(commonDenominator values : ℚ)*values index := by
  have hd : ((values index).den : ℚ)≠0 := by exact_mod_cast (values index).den_ne_zero
  simp only [commonNumerator,Int.cast_mul,Int.cast_natCast,Nat.cast_div (_p2mNS20 values index) hd]
  rw [←Rat.mul_den_eq_num (values index)]
  field_simp
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → AFT.RationalNumerics.commonNumerator_cast
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → _p2mNS18


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics.commonNumerator_div (values : Index → ℚ) (index : Index) :
    (commonNumerator values index : ℚ)/(commonDenominator values : ℚ)=values index := by
  rw [_p2mNS18]
  have hD : (commonDenominator values : ℚ)≠0 := by exact_mod_cast (_p2mNS16 values).ne'
  field_simp
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → AFT.RationalNumerics.commonNumerator_div
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → _p2mNS19


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics.commonDenominator_le (values : Index → ℚ) (bits : ℕ)
    (h : ∀index,HeightBound (values index) bits) :
    commonDenominator values≤2^(Fintype.card Index*bits) := by
  calc
    _ ≤ ∏ _index : Index,2^bits := Finset.prod_le_prod (fun index _ => Nat.zero_le _) (fun index _ => (h index).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←pow_mul];congr 1;ring
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → AFT.RationalNumerics.commonDenominator_le
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → _p2mNS15


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics.commonNumerator_abs_le (values : Index → ℚ) (bits : ℕ)
    (h : ∀index,HeightBound (values index) bits) (index : Index) :
    (commonNumerator values index).natAbs≤2^((Fintype.card Index+1)*bits) := by
  simp only [commonNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  calc
    _ ≤ 2^bits*commonDenominator values := Nat.mul_le_mul (h index).1 (Nat.div_le_self _ _)
    _ ≤ 2^bits*2^(Fintype.card Index*bits) := Nat.mul_le_mul_left _ (_p2mNS15 values bits h)
    _ = _ := by rw [←pow_add];congr 1;ring
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → AFT.RationalNumerics.commonNumerator_abs_le
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → _p2mNS17


end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → AFT.RationalNumerics.commonDenominator_le
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → _p2mNS15
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → AFT.RationalNumerics.commonDenominator_pos
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → _p2mNS16
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → AFT.RationalNumerics.commonNumerator_abs_le
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → _p2mNS17
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → AFT.RationalNumerics.commonNumerator_cast
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → _p2mNS18
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → AFT.RationalNumerics.commonNumerator_div
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → _p2mNS19
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → AFT.RationalNumerics.denominator_dvd_common
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → _p2mNS20


end
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → AFT.RationalNumerics.commonDenominator_pos
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → _p2mNS16
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → AFT.RationalNumerics.commonDenominator_le
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → _p2mNS15
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → AFT.RationalNumerics.commonNumerator_abs_le
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → _p2mNS17
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → AFT.RationalNumerics.commonNumerator_cast
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → _p2mNS18
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → AFT.RationalNumerics.commonNumerator_div
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → _p2mNS19
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → AFT.RationalNumerics.denominator_dvd_common
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → _p2mNS20


-- Source module: AFT.IntegerLinearIteration
section



/-! # Common-denominator iteration with linear operand bit growth -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Color : Type*} [Fintype Color]



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics.integerLinearIteration_exact (denominator : ℕ) (hd : 0<denominator)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ) (steps : ℕ) (output : Color) :
    (integerLinearIteration denominator matrix rhs steps output : ℚ)/(denominator : ℚ)^steps=
      linearIteration (fun out inp => (matrix out inp : ℚ)/denominator)
        (fun out => (rhs out : ℚ)/denominator) steps output := by
  have hd0 : (denominator : ℚ)≠0 := by exact_mod_cast hd.ne'
  induction steps generalizing output with
  | zero => simp [integerLinearIteration,linearIteration]
  | succ steps ih =>
    simp only [integerLinearIteration,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      Int.cast_sum,linearIteration,Pi.sub_apply,matrixApply]
    simp_rw [←ih]
    rw [sub_div,Finset.sum_div]
    congr 1
    · rw [pow_succ]
      field_simp
    · apply Finset.sum_congr rfl
      intro input _
      rw [pow_succ]
      field_simp
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → AFT.RationalNumerics.integerLinearIteration_exact
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → _p2mNS22


set_option maxRecDepth 8192
 theorem _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics.natAbs_finset_sum_le {Index : Type*} (set : Finset Index) (value : Index → ℤ) :
    (∑ index∈set,value index).natAbs≤∑ index∈set,(value index).natAbs := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hnot ih =>
    rw [Finset.sum_insert hnot,Finset.sum_insert hnot]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
open _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics renaming natAbs_finset_sum_le → AFT.RationalNumerics.natAbs_finset_sum_le
open _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics renaming natAbs_finset_sum_le → _p2mNS134




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics.integerLinearIteration_abs_le (denominator coefficientBits denominatorBits : ℕ)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ)
    (hden : denominator≤2^denominatorBits)
    (hmatrix : ∀output input,(matrix output input).natAbs≤2^coefficientBits)
    (hrhs : ∀output,(rhs output).natAbs≤2^coefficientBits)
    (steps : ℕ) (output : Color) :
    (integerLinearIteration denominator matrix rhs steps output).natAbs≤
      2^(steps*iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits) := by
  let slope := iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits
  have hds : denominatorBits ≤ slope := by dsimp [slope,iterationHeightSlope];omega
  induction steps generalizing output with
  | zero => simp [integerLinearIteration]
  | succ steps ih =>
    have hdpow : denominator^steps≤2^(steps*slope) := by
      calc
        _ ≤ (2^denominatorBits)^steps := Nat.pow_le_pow_left hden _
        _ = 2^(steps*denominatorBits) := by rw [←pow_mul];congr 1;ring
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hds)
    have hfirst : (rhs output*(denominator : ℤ)^steps).natAbs≤2^coefficientBits*2^(steps*slope) := by
      simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
      exact Nat.mul_le_mul (hrhs output) hdpow
    have hsum : (∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input).natAbs≤
        Fintype.card Color*(2^coefficientBits*2^(steps*slope)) := by
      apply (_p2mNS134 Finset.univ _).trans
      calc
        _ ≤ ∑ _input : Color,2^coefficientBits*2^(steps*slope) := by
          apply Finset.sum_le_sum
          intro input _
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul (hmatrix output input) (ih input)
        _ = _ := by simp
    have hcard : Fintype.card Color+1≤2^(Fintype.card Color+1) :=
      (Nat.lt_two_pow_self (n := Fintype.card Color+1)).le
    unfold integerLinearIteration
    calc
      _ ≤ (rhs output*(denominator : ℤ)^steps).natAbs+
          (∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input).natAbs := Int.natAbs_sub_le _ _
      _ ≤ 2^coefficientBits*2^(steps*slope)+Fintype.card Color*(2^coefficientBits*2^(steps*slope)) := Nat.add_le_add hfirst hsum
      _ = (Fintype.card Color+1)*(2^coefficientBits*2^(steps*slope)) := by ring
      _ ≤ 2^(Fintype.card Color+1)*(2^coefficientBits*2^(steps*slope)) := Nat.mul_le_mul_right _ hcard
      _ = 2^(Fintype.card Color+1+coefficientBits+steps*slope) := by simp only [pow_add];ring
      _ ≤ 2^((steps+1)*slope) := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [slope,iterationHeightSlope]
        nlinarith
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → AFT.RationalNumerics.integerLinearIteration_abs_le
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → _p2mNS21


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics.integerLinearIteration_height (denominator coefficientBits denominatorBits : ℕ)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ)
    (hden : denominator≤2^denominatorBits)
    (hmatrix : ∀output input,(matrix output input).natAbs≤2^coefficientBits)
    (hrhs : ∀output,(rhs output).natAbs≤2^coefficientBits)
    (steps : ℕ) (output : Color) :
    HeightBound ((integerLinearIteration denominator matrix rhs steps output : ℚ)/(denominator : ℚ)^steps)
      (steps*(iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits+denominatorBits)) := by
  have hnum := _p2mNS8 (_p2mNS21 denominator coefficientBits denominatorBits matrix rhs hden hmatrix hrhs steps output)
  have hden := (_p2mNS9 hden).pow steps
  convert hnum.div hden using 1
  ring
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → AFT.RationalNumerics.integerLinearIteration_height
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → _p2mNS23


end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → AFT.RationalNumerics.integerLinearIteration_abs_le
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → _p2mNS21
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → AFT.RationalNumerics.integerLinearIteration_exact
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → _p2mNS22
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → AFT.RationalNumerics.integerLinearIteration_height
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → _p2mNS23
open _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics renaming natAbs_finset_sum_le → AFT.RationalNumerics.natAbs_finset_sum_le
open _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics renaming natAbs_finset_sum_le → _p2mNS134


end
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → AFT.RationalNumerics.integerLinearIteration_exact
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → _p2mNS22
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → AFT.RationalNumerics.integerLinearIteration_abs_le
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → _p2mNS21
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → AFT.RationalNumerics.integerLinearIteration_height
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → _p2mNS23


-- Source module: AFT.RationalPiProgram
section


/-! # A finite rational program for pi with an explicit dyadic error

The program uses two convergent arctangent series and the proved identity
arctan(1/2)+arctan(1/3)=pi/4. No real-number oracle occurs in the program.
-/
namespace AFT.RationalNumerics
open scoped BigOperators





noncomputable section
open scoped Classical

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics.arctan_term_bound (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → AFT.RationalNumerics.arctan_term_bound
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → _p2mNS13


set_option maxRecDepth 8192
/-- On the two actual rational inputs, absolute geometric majorization
bounds the entire remaining series, including its alternating signs. -/
theorem _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics.arctanSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := _p2mNS13 (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → AFT.RationalNumerics.arctanSum_error
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → _p2mNS12


set_option maxRecDepth 8192
/-- `bits+3` terms of each short series give the requested binary accuracy. -/
theorem _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics.piApprox_error (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := _p2mNS12 (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := _p2mNS12 (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → AFT.RationalNumerics.piApprox_error
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → _p2mNS26


end
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → AFT.RationalNumerics.arctanSum_error
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → _p2mNS12
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → AFT.RationalNumerics.arctan_term_bound
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → _p2mNS13
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → AFT.RationalNumerics.piApprox_error
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → _p2mNS26

end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → AFT.RationalNumerics.arctanSum_error
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → _p2mNS12
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → AFT.RationalNumerics.arctan_term_bound
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → _p2mNS13
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → AFT.RationalNumerics.piApprox_error
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → _p2mNS26


end
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → AFT.RationalNumerics.arctanSum_error
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → _p2mNS12
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → AFT.RationalNumerics.arctan_term_bound
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → _p2mNS13
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → AFT.RationalNumerics.piApprox_error
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → _p2mNS26


-- Source module: AFT.LinearIterationHeight
section



/-! # Polynomial operand height in the materialized rational iteration -/
namespace AFT.RationalNumerics
open scoped BigOperators
variable {Color : Type*} [Fintype Color]

set_option maxRecDepth 8192
/-- A single common denominator is chosen for the stored matrix and rhs.
Consequently the bit bound is linear in the iteration count. -/
theorem _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics.linearIteration_height (matrix : Color → Color → ℚ) (rhs : Color → ℚ)
    (bits steps : ℕ) (hmatrix : ∀output input,HeightBound (matrix output input) bits)
    (hrhs : ∀output,HeightBound (rhs output) bits) (output : Color) :
    HeightBound (linearIteration matrix rhs steps output)
      (steps*((3*(Fintype.card Color^2+Fintype.card Color)+1)*bits+Fintype.card Color+1)) := by
  let values : (Color×Color)⊕Color → ℚ := Sum.elim (fun pair => matrix pair.1 pair.2) rhs
  let denominator := commonDenominator values
  let intMatrix := fun output input => commonNumerator values (Sum.inl (output,input))
  let intRhs := fun output => commonNumerator values (Sum.inr output)
  have hvalues : ∀index,HeightBound (values index) bits := by
    intro index
    cases index with
    | inl pair => exact hmatrix pair.1 pair.2
    | inr color => exact hrhs color
  have hc : Fintype.card ((Color×Color)⊕Color)=Fintype.card Color^2+Fintype.card Color := by
    simp [pow_two]
  have hd := _p2mNS15 values bits hvalues
  have hi := _p2mNS17 values bits hvalues
  rw [hc] at hd hi
  have hh := _p2mNS23 denominator ((Fintype.card Color^2+Fintype.card Color+1)*bits)
    ((Fintype.card Color^2+Fintype.card Color)*bits) intMatrix intRhs hd
    (fun output input => hi (Sum.inl (output,input))) (fun output => hi (Sum.inr output)) steps output
  rw [_p2mNS22 denominator (_p2mNS16 values)] at hh
  have hm : (fun out inp => (intMatrix out inp : ℚ)/denominator)=matrix := by
    funext out inp
    exact _p2mNS19 values (Sum.inl (out,inp))
  have hr : (fun out => (intRhs out : ℚ)/denominator)=rhs := by
    funext out
    exact _p2mNS19 values (Sum.inr out)
  rw [hm,hr] at hh
  convert hh using 1
  unfold iterationHeightSlope
  ring
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → AFT.RationalNumerics.linearIteration_height
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → _p2mNS24




end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → AFT.RationalNumerics.linearIteration_height
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → _p2mNS24


end
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → AFT.RationalNumerics.linearIteration_height
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → _p2mNS24


-- Source module: AFT.RationalGaussianResources
section



/-! # Polynomial iteration lengths for the actual root Gaussian program

These bounds describe the finite series lengths and integer exponents of the
executable rational program. They do not identify rational arithmetic with
constant-cost machine operations.
-/

namespace AFT.RationalNumerics

open scoped BigOperators









noncomputable section

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics.piApprox_le_five (bits : ℕ) : piApprox bits ≤ 5 := by
  have hp := (abs_le.mp (_p2mNS26 bits)).2
  have hden : (1 : ℝ) ≤ 2 ^ bits := one_le_pow₀ (by norm_num)
  have he : 1 / (2 : ℝ)^bits ≤ 1 := (div_le_one (by positivity)).mpr hden
  have hh : (piApprox bits : ℝ) ≤ 5 := by linarith [Real.pi_lt_four]
  exact_mod_cast hh
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → AFT.RationalNumerics.piApprox_le_five
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → _p2mNS27
















end
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → AFT.RationalNumerics.piApprox_le_five
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → _p2mNS27

end AFT.RationalNumerics
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → AFT.RationalNumerics.piApprox_le_five
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → _p2mNS27


end
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → AFT.RationalNumerics.piApprox_le_five
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → _p2mNS27


-- Source module: CurrentAFT.BinaryFiniteProduct
section



/-! # Counted fixed-length products of computed binary rationals -/
namespace CurrentAFT.BinaryFiniteProduct
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1400000



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct.current_value (count : ℕ) (term : Fin count → RationalResult) :
    (current count term).data.decode = ∏ index, (term index).data.decode := by
  induction count with
  | zero => simp only [current, one_value, Fin.prod_univ_zero]
  | succ count ih => simp only [current, RationalBits.multiply_value, ih, Fin.prod_univ_castSucc]
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → CurrentAFT.BinaryFiniteProduct.current_value
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → _p2mNS30












end CurrentAFT.BinaryFiniteProduct
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → CurrentAFT.BinaryFiniteProduct.current_value
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → _p2mNS30


end
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → CurrentAFT.BinaryFiniteProduct.current_value
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → _p2mNS30


-- Source module: CurrentAFT.Parameters
section


/-!
# The current manuscript's public parameter family

These definitions follow `sec:df-parameter-choice`, not the frozen V7
parameters. They are independent of the accuracy order. The least-prime
choice and its polynomial size are proved using Bertrand's theorem.
This file does not claim a polynomial-time implementation of prime search
or of the affine sampler.
-/

namespace CurrentAFT.Parameters











/- The checked witness contains both the actual least-prime search value
and its defining properties. Its opacity prevents the kernel from trying
to evaluate that search while comparing finite-alphabet instances. -/








set_option maxRecDepth 8192
/-- The opaque checked representation has exactly the original search
value, not merely some prime meeting a size bound. -/
theorem _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters.modulus_eq_find (security : ℕ) :
    modulus security = Nat.find (Nat.exists_infinite_primes (primeThreshold security)) := by
  apply Nat.le_antisymm
  · exact modulus_least security _
      (Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security))).1
      (Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security))).2
  · exact Nat.find_min' _ (modulus_spec security)
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → CurrentAFT.Parameters.modulus_eq_find
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → _p2mNS126




























-- Residue alphabets depend on this least-prime value. Keep the search
-- abstract during automatic typeclass normalization; explicit rewriting
-- with its definition remains available.


end CurrentAFT.Parameters
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → CurrentAFT.Parameters.modulus_eq_find
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → _p2mNS126


end
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → CurrentAFT.Parameters.modulus_eq_find
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → _p2mNS126


-- Source module: CurrentAFT.CurrentGaussianBits
section




/-! # Current Gaussian tables computed by Boolean-list arithmetic

The squared width is constructed by actual counter and binary encoding
programs. Every Gaussian series, rational normalization and array entry
is computed by the existing binary implementation. The cost is the
repository's explicit Boolean/list/counter work, not a TM compilation.
-/
namespace CurrentAFT.CurrentGaussianBits
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits Polynomial
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false















noncomputable section
open scoped Classical
attribute [local irreducible] widthCode table

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits.ratio_bounds (security cutoff : ℕ) (hcutoff : cutoff ≤ (security+2)^2) (point : Window cutoff) :
    0 ≤ gaussianRatio ((security+2 : ℚ)^2) point.val ∧
      gaussianRatio ((security+2 : ℚ)^2) point.val ≤ (security+2 : ℚ)^2 := by
  have hb : (0 : ℚ) < security+2 := by positivity
  have hp := Finset.mem_Icc.mp point.property
  have hlo : -(cutoff : ℚ) ≤ (point.val : ℚ) := by exact_mod_cast hp.1
  have hhi : (point.val : ℚ) ≤ (cutoff : ℚ) := by exact_mod_cast hp.2
  have hcut : (cutoff : ℚ) ≤ (security+2 : ℚ)^2 := by exact_mod_cast hcutoff
  have hproduct := mul_nonneg
    (show 0 ≤ (security+2 : ℚ)^2 + (point.val : ℚ) by linarith)
    (show 0 ≤ (security+2 : ℚ)^2 - (point.val : ℚ) by linarith)
  unfold gaussianRatio
  refine ⟨div_nonneg (sq_nonneg _) (pow_pos hb _).le, ?_⟩
  apply (div_le_iff₀ (pow_pos hb _)).mpr
  nlinarith only [hproduct]
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → CurrentAFT.CurrentGaussianBits.ratio_bounds
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → _p2mNS113




















end
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → CurrentAFT.CurrentGaussianBits.ratio_bounds
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → _p2mNS113

end CurrentAFT.CurrentGaussianBits
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → CurrentAFT.CurrentGaussianBits.ratio_bounds
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → _p2mNS113


end
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → CurrentAFT.CurrentGaussianBits.ratio_bounds
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → _p2mNS113


-- Source module: CurrentAFT.ProtectedCycle
section






/-!
# The actual protected latent cycle and its Fourier response

Independent latent edge scalars are sampled first, and every root is their
cyclic difference, including the closing edge. The endpoint law is a
pushforward of this whole product experiment; its roots are not replaced by
independent samples of their one-coordinate marginal.

The identities below are exact finite-distribution identities. Quantitative
centered likelihood bounds for randomly selected paths and the complete
calibration response-norm estimate remain separate obligations.
-/

namespace CurrentAFT.ProtectedCycle

open AFT
open scoped BigOperators Classical

noncomputable section







































set_option maxRecDepth 8192
/-- The entire two-coordinate marginal, rather than only product tests. -/
theorem _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle.independent_pair_law {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first) :
    (FiniteDist.independent reference).map (fun latent => (latent first, latent second)) =
      (reference first).prod (reference second) := by
  ext values
  have htest := independent_pair_expectation reference first second hdistinct
    (fun firstValue secondValue => if (firstValue, secondValue) = values then 1 else 0)
  have hleft : (FiniteDist.independent reference).expectation
      (fun latent => if (latent first, latent second) = values then 1 else 0) =
      ((FiniteDist.independent reference).map
        (fun latent => (latent first, latent second))).weight values := by
    simp only [FiniteDist.expectation, FiniteDist.map_weight, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro latent _
    by_cases hequal : (latent first, latent second) = values <;> simp [hequal]
  rw [hleft] at htest
  rw [htest]
  rcases values with ⟨firstValue, secondValue⟩
  simp [mul_ite, FiniteDist.prod_weight, ite_and]
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → CurrentAFT.ProtectedCycle.independent_pair_law
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → _p2mNS129




set_option maxRecDepth 8192
/-- Every nondegenerate cycle root has the independent two-edge difference
marginal. The theorem explicitly excludes a self-predecessor. -/
theorem _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle.cycleLaw_marginal {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (vertex : Fin body)
    (hdistinct : (finRotate body).symm vertex ≠ vertex) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value := by
  unfold cycleLaw differenceLaw
  rw [FiniteDist.map_map]
  have hpair := _p2mNS129 (fun _ : Fin body => edgeLaw) vertex
    ((finRotate body).symm vertex) hdistinct
  rw [← hpair, FiniteDist.map_map]
  rfl
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → CurrentAFT.ProtectedCycle.cycleLaw_marginal
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → _p2mNS127




set_option maxRecDepth 8192
/-- The one-root convolution holds for every actual body population at least two. -/
theorem _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (hbody : 2 ≤ body) (vertex : Fin body) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value :=
  _p2mNS127 body modulus edgeLaw value vertex (cycle_predecessor_ne body hbody vertex)
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → _p2mNS128










end
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → CurrentAFT.ProtectedCycle.cycleLaw_marginal
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → _p2mNS127
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → _p2mNS128
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → CurrentAFT.ProtectedCycle.independent_pair_law
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → _p2mNS129


end CurrentAFT.ProtectedCycle
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → CurrentAFT.ProtectedCycle.cycleLaw_marginal
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → _p2mNS127
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → _p2mNS128
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → CurrentAFT.ProtectedCycle.independent_pair_law
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → _p2mNS129


end
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → _p2mNS128
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → CurrentAFT.ProtectedCycle.cycleLaw_marginal
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → _p2mNS127
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → CurrentAFT.ProtectedCycle.independent_pair_law
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → _p2mNS129


-- Source module: CurrentAFT.CycleSelections
section



/-!
# Actual distinct body selections

Selections are finite embeddings and are sampled uniformly before the
latent cycle. Fixed selected coordinates retain their genuine joint law.
This file begins the centered-cycle analysis with the exact singleton
identity and actual two-position adjacency counting. The all-order forest
counting and centered-density norm estimates are separate obligations.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section













set_option maxRecDepth 8192
/-- Every selected coordinate has the same true two-edge convolution marginal. -/
theorem _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections.selectedLaw_coordinate {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) :
    (selectedLaw body order modulus source value sites).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [selectedLaw, FiniteDist.map_map]
  exact _p2mNS128 body modulus source value hbody (sites slot)
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → CurrentAFT.CycleSelections.selectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → _p2mNS124


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body) (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (slot : Fin order) :
    (averagedSelectedLaw body order modulus horder source value).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [averagedSelectedLaw, FiniteDist.map_mix]
  simp_rw [_p2mNS124 body order modulus hbody source value]
  exact FiniteDist.mix_const _ _
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → _p2mNS123










































end
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → _p2mNS123
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → CurrentAFT.CycleSelections.selectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → _p2mNS124


end CurrentAFT.CycleSelections
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → _p2mNS123
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → CurrentAFT.CycleSelections.selectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → _p2mNS124


end
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → CurrentAFT.CycleSelections.selectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → _p2mNS124
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → _p2mNS123


-- Source module: CurrentAFT.JointTaggedPhysicalFock
section




/-!
# Unpaired common-alphabet kernels and actual mixed physical channels

The original coefficient kernel is enlarged only by independent unused
coordinates. The paired four-output channel is then applied exactly once.
-/

namespace CurrentAFT.JointTaggedPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
  TaggedPhysicalFock OrdinaryPhysicalFock ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.JointTaggedPhysicalFock.classicalFinDecidableEq

attribute [local instance] _root_.CurrentAFT.JointTaggedPhysicalFock.classicalSumDecidableEq

attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount ProposalPrimary.primaryLaw

section Generic

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]































end Generic



































set_option maxRecDepth 8192
 theorem _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock.law_nonempty {State : Type*} [Fintype State] (law : FiniteDist State) : Nonempty State := by
  by_contra h
  haveI : IsEmpty State := not_nonempty_iff.mp h
  have := law.sum_one
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_ne_one] at this
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → CurrentAFT.JointTaggedPhysicalFock.law_nonempty
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → _p2mNS138










end
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → CurrentAFT.JointTaggedPhysicalFock.law_nonempty
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → _p2mNS138


end CurrentAFT.JointTaggedPhysicalFock
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → CurrentAFT.JointTaggedPhysicalFock.law_nonempty
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → _p2mNS138


end


-- Source module: CurrentAFT.TensorPublicProjection
section


/-! # Exact removal of unused coordinates in the common control alphabet -/
namespace CurrentAFT.TensorPublicProjection
open AFT JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TensorPublicProjection.finDecEq




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection.independent_decision_expectation {Index Color : Type*} [Fintype Index] [Fintype Color]
    (first second : DecidableEq Index) (law : Index → FiniteDist Color) (value : (Index → Color) → ℝ) :
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) first _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ first law) value =
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) second _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → CurrentAFT.TensorPublicProjection.independent_decision_expectation
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → _p2mNS133


section Generic
variable {Index Primary Body : Type*} [Fintype Index] [Fintype Primary] [Fintype Body]
  [DecidableEq Index]













end Generic



section TwoPools
variable {Primary Body Public : Type*} [Fintype Primary] [Fintype Body] [Fintype Public]



end TwoPools
end
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → CurrentAFT.TensorPublicProjection.independent_decision_expectation
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → _p2mNS133

end CurrentAFT.TensorPublicProjection
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → CurrentAFT.TensorPublicProjection.independent_decision_expectation
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → _p2mNS133


end
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → CurrentAFT.TensorPublicProjection.independent_decision_expectation
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → _p2mNS133


-- Source module: CurrentAFT.CyclePatternProgram
section








/-! # Fixed-order sparse cycle programs

Only latent edges touched by the supplied root positions are enumerated.
Adjacent selected roots read the same stored edge and the predecessor of
the first body position is still the closing edge. The program is a
finite rational sum, with its exact whole-body semantics proved below.
This is not yet the complete local physical-response evaluator.
-/
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false



















set_option maxRecDepth 8192
/-- The executable window enumeration preserves the original finite-sum value. -/
theorem _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram.gaussianEvaluate_eq_windowEvaluate {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) :
    gaussianEvaluate security cutoff bits sites test =
      evaluate sites (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
        (fun point : Window cutoff => point.val) test := by
  exact congrArg (fun enumeration : Fintype (Window cutoff) =>
    @evaluate (Window cutoff) ℤ enumeration inferInstance body order sites
      (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
      (fun point => point.val) test) (Subsingleton.elim _ _)
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → CurrentAFT.CyclePatternProgram.gaussianEvaluate_eq_windowEvaluate
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → _p2mNS119










noncomputable section
open scoped Classical

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram.restricted_expectation {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℝ) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
      test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot))))) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation (fun latent => test (roots sites value latent)) := by
  let embedding : touched sites ↪ Fin body := ⟨Subtype.val, Subtype.val_injective⟩
  have h := _p2mNS2
    (fun _ : Fin body => source) embedding (fun latent => test (roots sites value latent))
  apply Eq.trans (_p2mNS133
    (inferInstance : DecidableEq (Fin body)) (Classical.decEq _) (fun _ => source) _)
  apply Eq.trans h
  exact _p2mNS133 (Classical.decEq _)
    (inferInstance : DecidableEq (touched sites)) (fun _ => source) _
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → CurrentAFT.CyclePatternProgram.restricted_expectation
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → _p2mNS121


set_option maxRecDepth 8192
/-- The sparse rational program is exactly the complete independent latent
experiment for the supplied rational reference, for arbitrary joint tests. -/
theorem _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram.evaluate_local {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation
        (fun latent => (test (roots sites value latent) : ℝ)) := by
  simp only [evaluate, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, hweight,
    FiniteDist.expectation, FiniteDist.independent]
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → CurrentAFT.CyclePatternProgram.evaluate_local
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → _p2mNS117


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram.evaluate_semantics {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
        (test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot)))) : ℝ)) := by
  exact (_p2mNS117 sites source weight hweight value test).trans
    (_p2mNS121 sites source value (fun input => (test input : ℝ))).symm
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → CurrentAFT.CyclePatternProgram.evaluate_semantics
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → _p2mNS118


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) :
    (gaussianEvaluate security cutoff bits sites test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => windowApproxLaw
        (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation (fun latent =>
          (test (fun slot => (latent (sites slot)).val - (latent ((finRotate body).symm (sites slot))).val) : ℝ)) :=
by
  rw [_p2mNS119]
  exact _p2mNS118 sites _ _ (fun _ => rfl) _ test
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → _p2mNS120








set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram.averagedEvaluate_cast (security cutoff bits body order : ℕ) (hroom : order ≤ body)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) :
    (averagedEvaluate security cutoff bits body order test : ℝ) =
      (CycleSelections.selectionLaw body order hroom).expectation
        (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ)) := by
  have henumeration (first second : Fintype (Fin order ↪ Fin body)) (value : (Fin order ↪ Fin body) → ℝ) :
      ((@Fintype.card (Fin order ↪ Fin body) first : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) first, value state) =
        ((@Fintype.card (Fin order ↪ Fin body) second : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) second, value state) := by
    cases Subsingleton.elim first second
    rfl
  unfold averagedEvaluate
  simp only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    CycleSelections.selectionLaw, FiniteDist.expectation, FiniteDist.uniform_weight, ← Finset.mul_sum]
  exact henumeration (selectionFintype body order) (inferInstance : Fintype (Fin order ↪ Fin body))
    (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ))
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → CurrentAFT.CyclePatternProgram.averagedEvaluate_cast
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → _p2mNS116




end
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → CurrentAFT.CyclePatternProgram.averagedEvaluate_cast
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → _p2mNS116
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → CurrentAFT.CyclePatternProgram.evaluate_local
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → _p2mNS117
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → CurrentAFT.CyclePatternProgram.evaluate_semantics
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → _p2mNS118
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → _p2mNS120
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → CurrentAFT.CyclePatternProgram.restricted_expectation
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → _p2mNS121

end CurrentAFT.CyclePatternProgram
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → CurrentAFT.CyclePatternProgram.averagedEvaluate_cast
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → _p2mNS116
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → CurrentAFT.CyclePatternProgram.evaluate_local
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → _p2mNS117
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → CurrentAFT.CyclePatternProgram.evaluate_semantics
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → _p2mNS118
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → CurrentAFT.CyclePatternProgram.gaussianEvaluate_eq_windowEvaluate
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → _p2mNS119
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → _p2mNS120
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → CurrentAFT.CyclePatternProgram.restricted_expectation
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → _p2mNS121


end
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → CurrentAFT.CyclePatternProgram.averagedEvaluate_cast
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → _p2mNS116
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → CurrentAFT.CyclePatternProgram.gaussianEvaluate_eq_windowEvaluate
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → _p2mNS119
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → CurrentAFT.CyclePatternProgram.restricted_expectation
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → _p2mNS121
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → CurrentAFT.CyclePatternProgram.evaluate_local
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → _p2mNS117
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → CurrentAFT.CyclePatternProgram.evaluate_semantics
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → _p2mNS118
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → _p2mNS120


-- Source module: CurrentAFT.BinaryFullResponseCounts
section



/-! # Actual counts for full-response choices and root ordinals -/
namespace CurrentAFT.BinaryFullResponseCounts
open AFT RationalNumerics BinaryArithmetic
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProposalMetadata.counts differenceCounter doubleCounter







set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts.current_sizes (security : ℕ) :
    (current security).leg ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).ordinary ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).queue ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).body ≤ BinaryProposalMetadata.sizeBound security := by
  have h := BinaryProposalMetadata.counts_bounds security
  refine ⟨h.2.1,?_,h.1,h.2.2⟩
  change (differenceCounter (differenceCounter _ _).count _).count ≤ _
  rw [differenceCounter_value,differenceCounter_value]
  omega
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → CurrentAFT.BinaryFullResponseCounts.current_sizes
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → _p2mNS31










end CurrentAFT.BinaryFullResponseCounts
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → CurrentAFT.BinaryFullResponseCounts.current_sizes
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → _p2mNS31


end
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → CurrentAFT.BinaryFullResponseCounts.current_sizes
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → _p2mNS31


-- Source module: CurrentAFT.BinaryListSum
section


/-! # Executed rational sums over stored finite metadata lists -/
namespace CurrentAFT.BinaryListSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*}



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum.current_value (kernel : Index → RationalResult) (indices : List Index) :
    (current kernel indices).data.decode=(indices.map (fun index => (kernel index).data.decode)).sum := by
  induction indices with
  | nil => exact zero_value
  | cons index tail ih => simp only [current,RationalBits.add_value,ih,List.map_cons,List.sum_cons]
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → CurrentAFT.BinaryListSum.current_value
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → _p2mNS32

















end CurrentAFT.BinaryListSum
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → CurrentAFT.BinaryListSum.current_value
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → _p2mNS32


end
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → CurrentAFT.BinaryListSum.current_value
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → _p2mNS32


-- Source module: CurrentAFT.BinaryTouchedCycle
section





/-! Explicit touched-edge buffers for selected cycle roots. The candidates
are the selected edge and its cyclic predecessor. Duplicate removal compares
native stored vertex counters; no finite-choice enumeration is executed. -/
namespace CurrentAFT.BinaryTouchedCycle
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false




 

 




 

 




 

 

 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle.unique_length {body : ℕ} (items : List (Fin body)) : (unique items).value.length ≤ items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    change (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value).length ≤ _
    split_ifs <;> simp only [List.length_cons] <;> omega
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → CurrentAFT.BinaryTouchedCycle.unique_length
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → _p2mNS92


 




 

 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle.candidates_length {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (candidates hb sites).value.length = 2*count := by
  rw [candidates_value]
  simp only [List.length_flatMap,List.length_cons,List.length_nil]
  simp [Nat.mul_comm]
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → CurrentAFT.BinaryTouchedCycle.candidates_length
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → _p2mNS90


 




 

 

 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle.prepare_length {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (prepare hb sites).value.length ≤ 2*count := (_p2mNS92 _).trans_eq (_p2mNS90 hb sites)
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → CurrentAFT.BinaryTouchedCycle.prepare_length
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → _p2mNS91


end CurrentAFT.BinaryTouchedCycle
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → CurrentAFT.BinaryTouchedCycle.candidates_length
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → _p2mNS90
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → CurrentAFT.BinaryTouchedCycle.prepare_length
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → _p2mNS91
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → CurrentAFT.BinaryTouchedCycle.unique_length
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → _p2mNS92


end
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → CurrentAFT.BinaryTouchedCycle.candidates_length
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → _p2mNS90
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → CurrentAFT.BinaryTouchedCycle.unique_length
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → _p2mNS92
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → CurrentAFT.BinaryTouchedCycle.prepare_length
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → _p2mNS91


-- Source module: CurrentAFT.BinaryTouchedCycleBuffer
section


/-! Materialized touched-edge vectors and executed rank queries. The finite
bijection is used only to verify the Gaussian sum, never as a runtime lookup. -/
namespace CurrentAFT.BinaryTouchedCycleBuffer
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 

 




 

 

 

 




 

 




 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer.lookup_value {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (hmem : target ∈ values.toList) :
    values.get (lookup values hinj target hmem).value = target := by
  obtain ⟨index,he⟩ := (vector_mem_get values target).mp hmem
  have hr := rank_value values hinj target index (show values.get index = target from he) size le_rfl index.isLt
  simp only [lookup,hr,Option.get_some]
  exact he
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → CurrentAFT.BinaryTouchedCycleBuffer.lookup_value
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → _p2mNS93


 

noncomputable section



end
end CurrentAFT.BinaryTouchedCycleBuffer
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → CurrentAFT.BinaryTouchedCycleBuffer.lookup_value
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → _p2mNS93


end
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → CurrentAFT.BinaryTouchedCycleBuffer.lookup_value
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → _p2mNS93


-- Source module: CurrentAFT.BinaryTouchedCycleRanks
section


/-! The current/predecessor rank pair is materialized for every selected root
using the executed touched-edge lookup, before any Gaussian word is visited. -/
namespace CurrentAFT.BinaryTouchedCycleRanks
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle BinaryTouchedCycleBuffer
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false






 




 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks.positions_value {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (slot : Fin count) :
    (buffer hb sites).value.get ((positions hb sites).value.get slot).1 = sites.get slot ∧
    (buffer hb sites).value.get ((positions hb sites).value.get slot).2 = (finRotate body).symm (sites.get slot) := by
  simp only [positions,storeData_get,_p2mNS93,readVector_value,previous_value,and_self]
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → CurrentAFT.BinaryTouchedCycleRanks.positions_value
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → _p2mNS94





 

end CurrentAFT.BinaryTouchedCycleRanks
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → CurrentAFT.BinaryTouchedCycleRanks.positions_value
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → _p2mNS94


end
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → CurrentAFT.BinaryTouchedCycleRanks.positions_value
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → _p2mNS94


-- Source module: CurrentAFT.BinaryTupleSum
section




/-! # Explicit fixed-length tuple enumeration with binary sums

Tuple construction scans the stored tail.  The callback is charged on each
visit; the weight evaluator supplies a concrete joint-array reader.
-/
namespace CurrentAFT.BinaryTupleSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum.prepend_get {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) (index : Fin (count+1)) :
    ((prepend head tail).value.get index) = Fin.cons (α := fun _ => Value) head tail.get index := by
  refine Fin.cases ?_ (fun rest => ?_) index
  · simp [prepend]
  · simp [prepend, readVector_value]
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → CurrentAFT.BinaryTupleSum.prepend_get
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → _p2mNS97


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum.prepend_value {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) :
    (prepend head tail).value = Vector.ofFn (Fin.cons (α := fun _ => Value) head tail.get) := by
  apply Vector.ext
  intro index hi
  simpa only [Vector.get_eq_getElem, Vector.getElem_ofFn] using _p2mNS97 head tail ⟨index, hi⟩
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → CurrentAFT.BinaryTupleSum.prepend_value
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → _p2mNS98






set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum.get_ofFn_fun {Value : Type*} {count : ℕ} (word : Fin count → Value) :
    (Vector.ofFn word).get = word := by
  funext index
  exact Vector.get_ofFn word index
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → CurrentAFT.BinaryTupleSum.get_ofFn_fun
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → _p2mNS96




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum.current_value (pool count : ℕ) (kernel : Vector (Fin pool) count → RationalResult) :
    (current pool count kernel).data.decode =
      ∑ word : Fin count → Fin pool, (kernel (Vector.ofFn word)).data.decode := by
  induction count with
  | zero =>
    simp only [current, Fintype.sum_unique]
    congr 2
  | succ count ih =>
    rw [current, sumFin_value]
    simp_rw [ih]
    simp only [_p2mNS98, _p2mNS96]
    simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count+1) => Fin pool))
        (fun word => (kernel (Vector.ofFn word)).data.decode))
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → CurrentAFT.BinaryTupleSum.current_value
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → _p2mNS95
















end CurrentAFT.BinaryTupleSum
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → CurrentAFT.BinaryTupleSum.current_value
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → _p2mNS95
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → CurrentAFT.BinaryTupleSum.get_ofFn_fun
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → _p2mNS96
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → CurrentAFT.BinaryTupleSum.prepend_get
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → _p2mNS97
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → CurrentAFT.BinaryTupleSum.prepend_value
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → _p2mNS98


end
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → CurrentAFT.BinaryTupleSum.get_ofFn_fun
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → _p2mNS96
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → CurrentAFT.BinaryTupleSum.prepend_get
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → _p2mNS97
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → CurrentAFT.BinaryTupleSum.prepend_value
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → _p2mNS98
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → CurrentAFT.BinaryTupleSum.current_value
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → _p2mNS95


-- Source module: CurrentAFT.CurrentPublicShiftProgram
section




/-! Actual public-shift encoding by counter comparisons and signed binary arithmetic. -/

namespace CurrentAFT.CurrentPublicShiftProgram

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000



set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value (value : ℤ) : (encode value).value.decode = value := by
  cases value with
  | ofNat value => simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
  | negSucc value =>
    simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
    omega
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → CurrentAFT.CurrentPublicShiftProgram.encode_value
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → _p2mNS114
























end CurrentAFT.CurrentPublicShiftProgram
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → CurrentAFT.CurrentPublicShiftProgram.encode_value
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → _p2mNS114


end
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → CurrentAFT.CurrentPublicShiftProgram.encode_value
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → _p2mNS114


-- Source module: CurrentAFT.BinarySparseCycleEvaluation
section






/-! Literal binary Gaussian evaluation on the materialized touched edges.
All selected roots read the cached rank pair, so adjacent roots share exactly
the same latent edge coordinate. The closing predecessor is retained. -/
namespace CurrentAFT.BinarySparseCycleEvaluation
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false




 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation.rootEntry_value {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) :
    (rootEntry ranks word slot).value.decode =
      ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val := by
  simp only [rootEntry,readList_value]
  rw [List.getElem?_eq_getElem (by simpa only [Vector.length_toList] using slot.isLt)]
  simp only [Vector.getElem_toList,IntegerBits.subtract_value,_p2mNS114,readVector_value]
  rfl
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → CurrentAFT.BinarySparseCycleEvaluation.rootEntry_value
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → _p2mNS82





 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation.roots_value {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) :
    ((roots ranks word).value.get slot).decode =
      ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val := by
  rw [roots,storeData_get,_p2mNS82]
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → CurrentAFT.BinarySparseCycleEvaluation.roots_value
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → _p2mNS83





 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation.weightEntry_value {edges cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (word : Vector (Fin (2*cutoff+1)) edges) (edge : Fin edges) :
    (weightEntry weights word edge).data.decode = (weights.get (word.get edge)).decode := by
  simp only [weightEntry,readVector_value]
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → CurrentAFT.BinarySparseCycleEvaluation.weightEntry_value
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → _p2mNS85





 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation.term_value {edges count cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (ranks : Vector (Fin edges × Fin edges) count) (test : Vector IntegerBits count → RationalResult)
    (ideal : (Fin count → ℤ) → ℚ) (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode))
    (word : Vector (Fin (2*cutoff+1)) edges) :
    (term weights ranks test word).data.decode =
      (∏ edge, (weights.get (word.get edge)).decode) *
        ideal (fun slot => ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val) := by
  simp only [term,RationalBits.multiply_value,_p2mNS30,_p2mNS85,htest,_p2mNS83]
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → CurrentAFT.BinarySparseCycleEvaluation.term_value
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → _p2mNS84





 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation.current_tuple_value {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) (ideal : (Fin count → ℤ) → ℚ)
    (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode)) :
    (current security cutoff bits hb sites test).data.decode =
      ∑ word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1),
        (∏ edge, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits (word edge)) *
          ideal (fun slot => ((word (((positions hb sites).value.get slot).1)).val : ℤ) -
            (word (((positions hb sites).value.get slot).2)).val) := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [_p2mNS95]
  simp only [_p2mNS84 _ _ _ ideal htest,Vector.get_ofFn,CurrentGaussianBits.table_value]
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → CurrentAFT.BinarySparseCycleEvaluation.current_tuple_value
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → _p2mNS81


end CurrentAFT.BinarySparseCycleEvaluation
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → CurrentAFT.BinarySparseCycleEvaluation.current_tuple_value
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → _p2mNS81
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → CurrentAFT.BinarySparseCycleEvaluation.rootEntry_value
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → _p2mNS82
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → CurrentAFT.BinarySparseCycleEvaluation.roots_value
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → _p2mNS83
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → CurrentAFT.BinarySparseCycleEvaluation.term_value
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → _p2mNS84
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → CurrentAFT.BinarySparseCycleEvaluation.weightEntry_value
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → _p2mNS85


end
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → CurrentAFT.BinarySparseCycleEvaluation.rootEntry_value
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → _p2mNS82
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → CurrentAFT.BinarySparseCycleEvaluation.weightEntry_value
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → _p2mNS85
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → CurrentAFT.BinarySparseCycleEvaluation.current_tuple_value
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → _p2mNS81
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → CurrentAFT.BinarySparseCycleEvaluation.roots_value
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → _p2mNS83
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → CurrentAFT.BinarySparseCycleEvaluation.term_value
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → _p2mNS84


-- Source module: CurrentAFT.BinarySparseCycleSemantic
section


/-! The executed touched-edge Gaussian sum is exactly the manuscript's sparse
cycle evaluator, for arbitrary joint tests and every root-placement pattern. -/
namespace CurrentAFT.BinarySparseCycleSemantic
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false




 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic.coordinates_apply {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) (edge : Fin (prepare hb sites).value.length) :
    coordinates cutoff hb sites word (edgeEquiv hb sites edge) = FiniteConvolutionProgram.windowIndexEquiv cutoff (word edge) := by
  simp only [coordinates,Equiv.arrowCongr_apply,Function.comp_def,Equiv.symm_apply_apply]
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → CurrentAFT.BinarySparseCycleSemantic.coordinates_apply
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → _p2mNS86


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic.roots_coordinates {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) :
    CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) (coordinates cutoff hb sites word) =
      fun slot => ((word (((positions hb sites).value.get slot).1)).val : ℤ) -
        (word (((positions hb sites).value.get slot).2)).val := by
  funext slot
  have hcurrent : edgeEquiv hb sites ((positions hb sites).value.get slot).1 = CyclePatternProgram.currentEdge sites.get slot := by
    apply Subtype.ext
    exact (_p2mNS94 hb sites slot).1
  have hprevious : edgeEquiv hb sites ((positions hb sites).value.get slot).2 = CyclePatternProgram.previousEdge sites.get slot := by
    apply Subtype.ext
    exact (_p2mNS94 hb sites slot).2
  change ((coordinates cutoff hb sites word) (CyclePatternProgram.currentEdge sites.get slot)).val -
    ((coordinates cutoff hb sites word) (CyclePatternProgram.previousEdge sites.get slot)).val = _
  rw [←hcurrent,←hprevious,_p2mNS86,_p2mNS86]
  change (((word (((positions hb sites).value.get slot).1)).val : ℤ) - cutoff) -
    (((word (((positions hb sites).value.get slot).2)).val : ℤ) - cutoff) = _
  ring
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → CurrentAFT.BinarySparseCycleSemantic.roots_coordinates
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → _p2mNS89


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic.product_coordinates {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) :
    (∏ edge, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits (word edge)) =
      ∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge) := by
  have h := (edgeEquiv hb sites).prod_comp (fun edge =>
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge))
  simpa only [_p2mNS86,windowGaussianWeights] using h
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → CurrentAFT.BinarySparseCycleSemantic.product_coordinates
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → _p2mNS88


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic.current_value {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) (ideal : (Fin count → ℤ) → ℚ)
    (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode)) :
    (BinarySparseCycleEvaluation.current security cutoff bits hb sites test).data.decode =
      CyclePatternProgram.gaussianEvaluate security cutoff bits sites.get ideal := by
  rw [_p2mNS81 security cutoff bits hb sites test ideal htest]
  rw [_p2mNS119]
  unfold CyclePatternProgram.evaluate
  calc
    _ = ∑ word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1),
      (∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge)) *
        ideal (CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) (coordinates cutoff hb sites word)) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [_p2mNS88,_p2mNS89]
    _ = _ := (coordinates cutoff hb sites).sum_comp (fun latent : CyclePatternProgram.touched sites.get → Window cutoff =>
      (∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (latent edge)) *
        ideal (CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) latent))
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → _p2mNS87


end
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → CurrentAFT.BinarySparseCycleSemantic.coordinates_apply
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → _p2mNS86
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → _p2mNS87
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → CurrentAFT.BinarySparseCycleSemantic.product_coordinates
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → _p2mNS88
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → CurrentAFT.BinarySparseCycleSemantic.roots_coordinates
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → _p2mNS89

end CurrentAFT.BinarySparseCycleSemantic
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → CurrentAFT.BinarySparseCycleSemantic.coordinates_apply
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → _p2mNS86
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → _p2mNS87
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → CurrentAFT.BinarySparseCycleSemantic.product_coordinates
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → _p2mNS88
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → CurrentAFT.BinarySparseCycleSemantic.roots_coordinates
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → _p2mNS89


end
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → CurrentAFT.BinarySparseCycleSemantic.coordinates_apply
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → _p2mNS86
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → CurrentAFT.BinarySparseCycleSemantic.product_coordinates
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → _p2mNS88
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → _p2mNS87
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → CurrentAFT.BinarySparseCycleSemantic.roots_coordinates
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → _p2mNS89


-- Source module: CurrentAFT.CycleRootExpansion
section




/-!
# Exact finite response expansion for the actual permuted closed cycle

The response acts on arbitrary joint, vector-valued tests. Its source law
is the literal uniform body permutation of the complete protected cycle.
The independent term and all singleton cancellations are proved under
support-only positivity, so no inverse of a zero root atom is used.
-/

namespace CurrentAFT.CycleRootExpansion

open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]



















section Actual

attribute [local instance] _root_.CurrentAFT.CycleRootExpansion.currentModulusNeZero











set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion.current_body_two_le (security : ℕ) : 2 ≤ Parameters.bodySize security := by
  have hbase := Parameters.base_ge_two security
  have hmod := (Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (Parameters.modulus security) hpower)
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → _p2mNS122


















variable {Control : Type*} [Fintype Control]



end Actual
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → _p2mNS122


end
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → _p2mNS122


end CurrentAFT.CycleRootExpansion
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → _p2mNS122


end
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → _p2mNS122


-- Source module: CurrentAFT.CurrentCycleEntryProgram
section




/-! # Sparse rational entries of the actual selected closed-cycle law

Only ordered distinct selected sites and their touched latent edges are
enumerated. The full body permutation and all unused latent coordinates
are eliminated by exact probability identities. Every entry test below
is an explicit modular indicator, not an input oracle.
-/
namespace CurrentAFT.CurrentCycleEntryProgram

open AFT GaussianSource CycleSelections CyclePatternProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false







noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

attribute [local instance] _root_.CurrentAFT.CurrentCycleEntryProgram.modulusNeZero


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq (security : ℕ) : bodyCount security = Parameters.bodySize security := by
  simp only [bodyCount, PublicParameterProgram.modulus_value, Parameters.bodySize_eq, Parameters.base]
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → _p2mNS109




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff (security order : ℕ) (roots : Fin order → ℤ)
    (output : Fin order → CycleRootExpansion.Root security) :
    (∀ index, roots index % Parameters.modulus security = ((output index).val : ℤ)) ↔
      (fun index => (roots index : CycleRootExpansion.Root security)) = output := by
  have hpoint (integer : ℤ) (color : CycleRootExpansion.Root security) :
      integer % Parameters.modulus security = (color.val : ℤ) ↔
        (integer : CycleRootExpansion.Root security) = color := by
    rw [← ZMod.val_intCast]
    constructor
    · intro hequal
      apply ZMod.val_injective
      exact Int.ofNat_inj.mp hequal
    · intro hequal
      rw [hequal]
  constructor
  · intro h
    funext index
    exact (hpoint _ _).mp (h index)
  · intro h index
    exact (hpoint _ _).mpr (congrFun h index)
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → _p2mNS110


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram.selected_probability_source (security order : ℕ)
    (source : FiniteDist (Window (edgeCutoff security)))
    (sites : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => source)).expectation
      (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
        (fun slot => (latent (sites slot)).val -
          (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ)) =
      (selectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        (source) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security)) sites).weight output := by
  rw [selectedLaw, ProtectedCycle.cycleLaw, FiniteDist.map_map]
  simp only [FiniteDist.expectation, FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro latent _
  have hequal : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output ↔
      ∀ slot, ((latent (sites slot)).val -
        (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) %
          Parameters.modulus security = ((output slot).val : ℤ) := by
    rw [_p2mNS110]
    simp only [PublicCharge.cycleDifference, Int.cast_sub]
  unfold pointTest
  by_cases hactual : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output
  · simp only [if_pos hactual, if_pos (hequal.mp hactual), Rat.cast_one, mul_one]
  · have hmod := mt hequal.mpr hactual
    simp only [if_neg hactual, if_neg hmod, Rat.cast_zero, mul_zero]
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → CurrentAFT.CurrentCycleEntryProgram.selected_probability_source
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → _p2mNS112







set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → CycleRootExpansion.Root security) :
    (selectedEntry security bits order (fun index => (output index).val) : ℝ) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output := by
  unfold selectedEntry
  rw [_p2mNS109, PublicParameterProgram.modulus_value,
    _p2mNS116 security (edgeCutoff security) bits (Parameters.bodySize security) order hroom]
  simp_rw [_p2mNS120, _p2mNS112]
  rfl
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → _p2mNS111






end
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → _p2mNS109
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → _p2mNS110
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → _p2mNS111
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → CurrentAFT.CurrentCycleEntryProgram.selected_probability_source
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → _p2mNS112

end CurrentAFT.CurrentCycleEntryProgram
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → _p2mNS109
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → _p2mNS110
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → _p2mNS111
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → CurrentAFT.CurrentCycleEntryProgram.selected_probability_source
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → _p2mNS112


end
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → CurrentAFT.CurrentCycleEntryProgram.selected_probability_source
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → _p2mNS112
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → _p2mNS110
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → _p2mNS109
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → _p2mNS111


-- Source module: CurrentAFT.RootSignedMassProgram
section



/-! # Root centering as a signed mass with no root-atom inverse

After multiplication by its actual root-reference mass, the selected
coefficient is an expectation of products `delta - marginal`. This is an
identity of coefficient data, before physical evaluation. The rational
program evaluates those explicit bounded tests on sparse cycle patterns.
-/
namespace CurrentAFT.RootSignedMassProgram

open AFT GaussianSource CycleSelections CyclePatternProgram CycleRootExpansion
  CurrentCycleEntryProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false









noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

attribute [local instance] _root_.CurrentAFT.RootSignedMassProgram.modulusNeZero






set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram.singleton_probability (security : ℕ) (source : FiniteDist (Window (edgeCutoff security)))
    (output : Root security) :
    (averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := _p2mNS122 security; omega) source
      (fun scalar => ((scalar.val : ℤ) : Root security))).weight (fun _ => output) =
        (ProtectedCycle.differenceLaw source (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  have h := congrArg (fun law : FiniteDist (Root security) => law.weight output)
    (_p2mNS123 (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := _p2mNS122 security; omega) (_p2mNS122 security) source
      (fun scalar => ((scalar.val : ℤ) : Root security)) 0)
  change ((averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security) _ source _).map
    (oneEquiv (Root security))).weight output = _ at h
  rw [FiniteDist.map_equiv_weight] at h
  exact h
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → CurrentAFT.RootSignedMassProgram.singleton_probability
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → _p2mNS132


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram.referenceEntry_cast (security bits : ℕ) (output : Root security) :
    (referenceEntry security bits output.val : ℝ) =
      (ProtectedCycle.differenceLaw
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  rw [referenceEntry, _p2mNS111 security bits 1 (by have := _p2mNS122 security; omega)
    (fun _ => output), _p2mNS132]
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → CurrentAFT.RootSignedMassProgram.referenceEntry_cast
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → _p2mNS131






















end
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → CurrentAFT.RootSignedMassProgram.referenceEntry_cast
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → _p2mNS131
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → CurrentAFT.RootSignedMassProgram.singleton_probability
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → _p2mNS132

end CurrentAFT.RootSignedMassProgram
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → CurrentAFT.RootSignedMassProgram.referenceEntry_cast
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → _p2mNS131
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → CurrentAFT.RootSignedMassProgram.singleton_probability
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → _p2mNS132


end
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → CurrentAFT.RootSignedMassProgram.referenceEntry_cast
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → _p2mNS131
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → CurrentAFT.RootSignedMassProgram.singleton_probability
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → _p2mNS132


-- Source module: CurrentAFT.CurrentRootSlotIndex
section


/-! Bounded native lookup of each tagged root in the active groups.
There are two candidate root slots per group; the second slot of an
ordinary or retained group is explicitly rejected. -/
namespace CurrentAFT.CurrentRootSlotIndex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false































set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex.tagPosition_eq {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) :
    tagPosition selection tagged ordering tag =
      (ordering.symm (tagEmbedding selection tagged tag).fst,
        slotNumber selection tagged (tagEmbedding selection tagged tag)) := by
  unfold tagPosition
  simp only [position_tag, Option.get_some, encode, Equiv.symm_apply_apply]
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → CurrentAFT.CurrentRootSlotIndex.tagPosition_eq
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → _p2mNS115




end CurrentAFT.CurrentRootSlotIndex
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → CurrentAFT.CurrentRootSlotIndex.tagPosition_eq
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → _p2mNS115


end
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → CurrentAFT.CurrentRootSlotIndex.tagPosition_eq
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → _p2mNS115


-- Source module: CurrentAFT.RationalScalarFamilyAverage
section



/-! # Averaging complete coefficient tables under the one shared scalar -/
namespace CurrentAFT.RationalScalarFamilyAverage
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus



noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalScalarFamilyAverage.scalarAverageFinDecidableEq


set_option maxRecDepth 8192
/-- The executable enumeration equals the original shared-scalar window average. -/
theorem _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ℕ)
    (centers : Fin arity.val.2.val → ℕ) :
    current security bits order table arity colors centers =
      ∑ scalar : Window (RationalBackgroundLinearProgram.cutoff security),
        RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
          table scalar.val arity colors centers := by
  unfold current
  exact (FiniteConvolutionProgram.windowIndexEquiv (RationalBackgroundLinearProgram.cutoff security)).sum_comp
    (fun scalar : Window (RationalBackgroundLinearProgram.cutoff security) =>
      RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
        table scalar.val arity colors centers)
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → _p2mNS130










end
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → _p2mNS130

end CurrentAFT.RationalScalarFamilyAverage
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → _p2mNS130


end
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → _p2mNS130


-- Source module: CurrentAFT.FullResponseEnumeration
section


/-! # Polynomial-size root-tag enumeration in the actual full response

All subsets with at most the fixed truncation order are generated as the
images of bounded-length words. The algorithm never forms the powerset
of the body population before filtering it by cardinality.
-/
namespace CurrentAFT.FullResponseEnumeration

open AFT ActualBlockFock ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false





noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration.mem_boundedSubsets {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (subset : Finset Pool) : subset ∈ boundedSubsets Pool order ↔ subset.card ≤ order := by
  constructor
  · intro hsubset
    obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hsubset
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin word.1.val))) (f := word.2)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    exact hc.trans (by have := word.1.isLt; omega)
  · intro hcard
    let number : Fin subset.card ≃ subset :=
      (Fintype.equivFinOfCardEq (show Fintype.card subset = subset.card by simp)).symm
    let word : SubsetWords Pool order := ⟨⟨subset.card, by omega⟩, fun index => (number index).val⟩
    refine Finset.mem_image.mpr ⟨word, Finset.mem_univ _, ?_⟩
    ext point
    constructor
    · intro hpoint
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hpoint
      exact (number index).property
    · intro hpoint
      refine Finset.mem_image.mpr ⟨number.symm ⟨point, hpoint⟩, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val (number.apply_symm_apply ⟨point, hpoint⟩)
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → CurrentAFT.FullResponseEnumeration.mem_boundedSubsets
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → _p2mNS125












end
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → CurrentAFT.FullResponseEnumeration.mem_boundedSubsets
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → _p2mNS125

end CurrentAFT.FullResponseEnumeration
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → CurrentAFT.FullResponseEnumeration.mem_boundedSubsets
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → _p2mNS125


end
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → CurrentAFT.FullResponseEnumeration.mem_boundedSubsets
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → _p2mNS125


-- Source module: CurrentAFT.BinaryRootMetadataSerializer
section





/-! Bounded serialization of selected controls and sorted root tags.
The executed filter visits only the supplied tags; candidate root lookup
visits two slots per selected or retained group. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic RationalRejectionProgram RationalRootGroupProgram
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

























set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer.kept_length_le {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : (kept primary body tagged).value.length ≤ tags := by
  rw [kept_value]
  simpa only [Vector.length_toList] using List.length_filter_le (fun block => (isKept primary body block).value) tagged.toList
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → CurrentAFT.BinaryRootMetadataSerializer.kept_length_le
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → _p2mNS57












set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer.find_value {α : Type*} (test : α → CountedValue Bool) (items : List α) :
    (find test items).value=items.find? (fun item => (test item).value) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases h : (test head).value <;> simp only [find,List.find?_cons,h,ih,Bool.false_eq_true,ite_false,ite_true]
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → CurrentAFT.BinaryRootMetadataSerializer.find_value
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → _p2mNS52






set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer.splitIndex_value {groups : ℕ} (index : Fin (groups*2)) :
    (splitIndex index).value=finProdFinEquiv.symm index := by
  apply Prod.ext <;> apply Fin.ext
  · exact (divideCounter_value index.val 2 (by omega)).1
  · exact (divideCounter_value index.val 2 (by omega)).2
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → CurrentAFT.BinaryRootMetadataSerializer.splitIndex_value
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → _p2mNS74












set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer.current_kept_le {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : (current primary body tagged).kept ≤ tags :=
  _p2mNS57 primary body tagged
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → CurrentAFT.BinaryRootMetadataSerializer.current_kept_le
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → _p2mNS43


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer.current_role {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin (groupCount primary body tagged)) :
    (current primary body tagged).data.roles.get index=(role primary body (kept primary body tagged).value index).value :=
  storeData_get _ _ _
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → CurrentAFT.BinaryRootMetadataSerializer.current_role
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → _p2mNS48


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) :
    (current primary body tagged).data.tagged.get index=(tagSlot primary body tagged index).value :=
  storeData_get _ _ _
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → _p2mNS50


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer.candidate_primary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hg : group.val<r) :
    (candidate primary body retained group slot).value=
      some (if slot.val=0 then legs+(primary.get ⟨group.val,hg⟩).val else (primary.get ⟨group.val,hg⟩).val) := by
  have hp := (lessCounter_value group.val r).mpr hg
  simp only [candidate,dif_pos hp,readVector_value,addCounter_value,equalCounter_value]
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → CurrentAFT.BinaryRootMetadataSerializer.candidate_primary
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → _p2mNS38


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer.candidate_ordinary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hp : ¬group.val<r) (hg : group.val<r+s) :
    (candidate primary body retained group slot).value=
      if slot.val=0 then some (legs+legs+(body.get ⟨group.val-r,by omega⟩).val) else none := by
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond := (lessCounter_value group.val (r+s)).mpr hg
  simp only [candidate,dif_neg hfirst,dif_pos hsecond,readVector_value,addCounter_value,
    differenceCounter_value,equalCounter_value]
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → CurrentAFT.BinaryRootMetadataSerializer.candidate_ordinary
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → _p2mNS37


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer.candidate_kept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hg : ¬group.val<r+s) :
    (candidate primary body retained group slot).value=
      if slot.val=0 then some (retained.get ⟨group.val-(r+s),by have := group.isLt;omega⟩).val else none := by
  have hp : ¬group.val<r := by omega
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond : ¬(lessCounter group.val (r+s)).value=true := by simpa only [lessCounter_value] using hg
  simp only [candidate,dif_neg hfirst,dif_neg hsecond,readList_value,differenceCounter_value,equalCounter_value]
  rw [List.getElem?_eq_getElem (by have := group.isLt;omega)]
  rfl
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → CurrentAFT.BinaryRootMetadataSerializer.candidate_kept
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → _p2mNS36


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer.role_primary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hg : group.val<r) : (role primary body retained group).value=.primary := by
  have hp := (lessCounter_value group.val r).mpr hg
  simp only [role,hp,ite_true]
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → CurrentAFT.BinaryRootMetadataSerializer.role_primary
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → _p2mNS73


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer.role_ordinary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hp : ¬group.val<r) (hg : group.val<r+s) : (role primary body retained group).value=.ordinary := by
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond := (lessCounter_value group.val (r+s)).mpr hg
  simp only [role,if_neg hfirst,if_pos hsecond]
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → CurrentAFT.BinaryRootMetadataSerializer.role_ordinary
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → _p2mNS72


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer.role_kept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hg : ¬group.val<r+s) :
    (role primary body retained group).value=
      let value := (retained.get ⟨group.val-(r+s),by have := group.isLt;omega⟩).val
      if value<legs then .leg else if value<legs+(legs+ordinary) then .center else .queue := by
  have hp : ¬group.val<r := by omega
  simp only [role,lessCounter_value,if_neg hp,if_neg hg,readList_value,differenceCounter_value,addCounter_value]
  rw [List.getElem?_eq_getElem (by have := group.isLt;omega)]
  rfl
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → CurrentAFT.BinaryRootMetadataSerializer.role_kept
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → _p2mNS71


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_value {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (index : Fin (((r+s)+retained.length)*2)) :
    (matchesBlock primary body retained block index).value=
      ((candidate primary body retained (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value).any
        (fun number => decide (number=block.val)) := by
  simp only [matchesBlock,_p2mNS74]
  cases h : (candidate primary body retained (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value with
  | none => rfl
  | some number =>
    simp only [Option.any_some]
    exact Bool.eq_iff_iff.mpr (by simp only [equalCounter_value,decide_eq_true_eq])
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_value
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → _p2mNS59






end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → CurrentAFT.BinaryRootMetadataSerializer.candidate_kept
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → _p2mNS36
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → CurrentAFT.BinaryRootMetadataSerializer.candidate_ordinary
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → _p2mNS37
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → CurrentAFT.BinaryRootMetadataSerializer.candidate_primary
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → _p2mNS38
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → CurrentAFT.BinaryRootMetadataSerializer.current_kept_le
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → _p2mNS43
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → CurrentAFT.BinaryRootMetadataSerializer.current_role
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → _p2mNS48
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → _p2mNS50
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → CurrentAFT.BinaryRootMetadataSerializer.find_value
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → _p2mNS52
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → CurrentAFT.BinaryRootMetadataSerializer.kept_length_le
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → _p2mNS57
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_value
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → _p2mNS59
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → CurrentAFT.BinaryRootMetadataSerializer.role_kept
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → _p2mNS71
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → CurrentAFT.BinaryRootMetadataSerializer.role_ordinary
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → _p2mNS72
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → CurrentAFT.BinaryRootMetadataSerializer.role_primary
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → _p2mNS73
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → CurrentAFT.BinaryRootMetadataSerializer.splitIndex_value
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → _p2mNS74


end
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → CurrentAFT.BinaryRootMetadataSerializer.current_kept_le
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → _p2mNS43
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → CurrentAFT.BinaryRootMetadataSerializer.candidate_kept
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → _p2mNS36
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → CurrentAFT.BinaryRootMetadataSerializer.role_kept
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → _p2mNS71
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → _p2mNS50
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → CurrentAFT.BinaryRootMetadataSerializer.current_role
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → _p2mNS48
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → CurrentAFT.BinaryRootMetadataSerializer.splitIndex_value
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → _p2mNS74
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → CurrentAFT.BinaryRootMetadataSerializer.find_value
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → _p2mNS52
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → CurrentAFT.BinaryRootMetadataSerializer.kept_length_le
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → _p2mNS57
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → CurrentAFT.BinaryRootMetadataSerializer.candidate_primary
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → _p2mNS38
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_value
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → _p2mNS59
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → CurrentAFT.BinaryRootMetadataSerializer.role_primary
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → _p2mNS73
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → CurrentAFT.BinaryRootMetadataSerializer.candidate_ordinary
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → _p2mNS37
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → CurrentAFT.BinaryRootMetadataSerializer.role_ordinary
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → _p2mNS72


-- Source module: CurrentAFT.BinaryRootMetadataMeaning
section


/-! Exact ordinal meaning of the bounded root metadata serialization. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize







 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer.tagsInput_get {security : ℕ} (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (tagsInput tagged).get index=numbering security (CurrentRootOrdering.tagOrdering tagged index).val :=
  Vector.get_ofFn _ _
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → CurrentAFT.BinaryRootMetadataSerializer.tagsInput_get
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → _p2mNS77



























set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer.keptOrdering_number {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin (CurrentRootOrdering.keptIndices selection tagged).card) :
    CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.keptOrdering selection tagged index).val.val=
      (Finset.orderIsoOfFin (CurrentRootOrdering.keptIndices selection tagged) rfl index).val := by
  exact (CurrentRootOrdering.blockNumbering security).apply_symm_apply _
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → CurrentAFT.BinaryRootMetadataSerializer.keptOrdering_number
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → _p2mNS56


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer.retainedInput_get {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin (retainedInput choice tagged).length) :
    (retainedInput choice tagged).get index=
      numbering security (CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged
        (finCongr (retainedInput_length choice tagged) index)).val.val := by
  classical
  let selection := RationalFullResponseProgram.selection security r s choice
  let items := retainedInput choice tagged
  let output : Fin items.length → Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
    fun index => numbering security (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) index)).val.val
  have hc : items.toFinset.card=items.length := List.toFinset_card_of_nodup (retainedInput_nodup choice tagged)
  have hm : StrictMono items.get := List.pairwise_iff_get.mp (retainedInput_increasing choice tagged)
  have ho : StrictMono output := by
    intro i j hij
    change (CurrentRootOrdering.blockNumbering security
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) i)).val.val).val<
      (CurrentRootOrdering.blockNumbering security
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) j)).val.val).val
    rw [_p2mNS56,_p2mNS56]
    exact (Finset.orderIsoOfFin (CurrentRootOrdering.keptIndices selection tagged) rfl).strictMono hij
  have hg (i : Fin items.length) : output i∈items.toFinset := by
    rw [List.mem_toFinset]
    apply (retainedInput_membership choice tagged _).mpr
    change (numbering security).symm (numbering security _ )∈_
    rw [Equiv.symm_apply_apply]
    exact ((CurrentRootOrdering.keptTagsEquiv selection tagged).symm
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) i))).property
  have hget := Finset.orderEmbOfFin_unique hc (fun i => List.mem_toFinset.mpr (List.get_mem items i)) hm
  have hout := Finset.orderEmbOfFin_unique hc hg ho
  exact congrFun (hget.trans hout.symm) index
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_get
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → _p2mNS69


end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → CurrentAFT.BinaryRootMetadataSerializer.keptOrdering_number
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → _p2mNS56
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_get
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → _p2mNS69
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → CurrentAFT.BinaryRootMetadataSerializer.tagsInput_get
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → _p2mNS77


end
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → CurrentAFT.BinaryRootMetadataSerializer.tagsInput_get
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → _p2mNS77
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → CurrentAFT.BinaryRootMetadataSerializer.keptOrdering_number
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → _p2mNS56
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_get
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → _p2mNS69


-- Source module: CurrentAFT.BinaryRootMetadataActual
section


/-! The executed role and tagged-slot arrays agree with the actual sorted
active-group numbering. All cardinal transports are proof-only. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize







 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_primary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    ((inputOrdering choice tagged).symm (.inl (.inl index))).val=index.val := rfl
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_primary
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → _p2mNS55


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_ordinary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    ((inputOrdering choice tagged).symm (.inl (.inr index))).val=r+index.val := rfl
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_ordinary
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → _p2mNS54


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_kept {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (index : HitKept (RationalFullResponseProgram.selection security r s choice) tagged) :
    ((inputOrdering choice tagged).symm (.inr index)).val=(r+s)+
      ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).val := rfl
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_kept
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → _p2mNS53


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer.retainedInput_at_group {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (index : HitKept (RationalFullResponseProgram.selection security r s choice) tagged) :
    (retainedInput choice tagged).get
      ⟨((inputOrdering choice tagged).symm (.inr index)).val-(r+s),by
        rw [_p2mNS53]
        have h := ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).isLt
        have hlen := retainedInput_length choice tagged
        omega⟩ = numbering security index.val.val := by
  rw [_p2mNS69]
  have hi : finCongr (retainedInput_length choice tagged)
      (⟨((inputOrdering choice tagged).symm (.inr index)).val-(r+s),by
        rw [_p2mNS53]
        have h := ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).isLt
        have hlen := retainedInput_length choice tagged
        omega⟩ : Fin (retainedInput choice tagged).length)=
      (CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index := by
    apply Fin.ext
    simp only [finCongr_apply,Fin.val_cast,_p2mNS53]
    omega
  rw [hi,Equiv.apply_symm_apply]
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_at_group
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → _p2mNS68


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer.candidate_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (group : ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged) (slot : Fin 2) :
    (candidate (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm group) slot).value =
      (CurrentRootSlotIndex.within (RationalFullResponseProgram.selection security r s choice) tagged group slot).map
        (fun root => (numbering security (CurrentRootSlotIndex.rootBlock (RationalFullResponseProgram.selection security r s choice) tagged root)).val) := by
  rcases group with (primary | ordinary) | retained
  · have hg : ((inputOrdering choice tagged).symm (.inl (.inl primary))).val<r := by
      rw [_p2mNS55]
      exact primary.isLt
    rw [_p2mNS38 (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inl (.inl primary))) slot hg]
    simp only [primaryInput,Vector.get_ofFn,CurrentRootSlotIndex.within,Option.map_some,CurrentRootSlotIndex.rootBlock]
    split_ifs
    · simp only [numbering_compensator]
      apply congrArg (fun index : Fin r => some (Parameters.legCount security+(choice.1 index).val))
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inl primary))).val=primary.val
      exact _p2mNS55 choice tagged primary
    · simp only [numbering_primary]
      apply congrArg (fun index : Fin r => some (choice.1 index).val)
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inl primary))).val=primary.val
      exact _p2mNS55 choice tagged primary
  · have hp : ¬((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val<r := by
      rw [_p2mNS54]
      omega
    have hg : ((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val<r+s := by
      rw [_p2mNS54]
      have := ordinary.isLt
      omega
    rw [_p2mNS37 (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inl (.inr ordinary))) slot hp hg]
    simp only [ordinaryInput,Vector.get_ofFn,CurrentRootSlotIndex.within]
    split_ifs
    · simp only [Option.map_some,CurrentRootSlotIndex.rootBlock,numbering_ordinary]
      apply congrArg (fun index : Fin s => some (Parameters.legCount security+Parameters.legCount security+(choice.2 index).val))
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val-r=ordinary.val
      have hval := _p2mNS54 choice tagged ordinary
      omega
    · rfl
  · have hg : ¬((inputOrdering choice tagged).symm (.inr retained)).val<r+s := by
      rw [_p2mNS53]
      omega
    rw [_p2mNS36 (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inr retained)) slot hg]
    rw [_p2mNS68]
    simp only [CurrentRootSlotIndex.within]
    split_ifs <;> simp only [Option.map_some,Option.map_none,CurrentRootSlotIndex.rootBlock]
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → CurrentAFT.BinaryRootMetadataSerializer.candidate_input
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → _p2mNS35





 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer.classify_numbering (security : ℕ) (block : BlockIndex security) :
    (if (numbering security block).val<Parameters.legCount security then RationalRootGroupProgram.LocalRole.leg else
      if (numbering security block).val<Parameters.legCount security+(Parameters.legCount security+BackgroundRates.ordinaryPool security) then .center else .queue)=keptRole block := by
  have hs := UniformTaggedOutput.centerCount_split security
  rcases block with leg | (center | queue)
  · rw [numbering_primary]
    exact if_pos leg.isLt
  · have hv : (numbering security (.inr (.inl center))).val=Parameters.legCount security+center.val := rfl
    rw [hv,if_neg (by omega),if_pos (by have := center.isLt;omega)]
    rfl
  · have hv : (numbering security (.inr (.inr queue))).val=Parameters.legCount security+centerCount security+queue.val := by
      change Parameters.legCount security+(centerCount security+queue.val)=_
      omega
    rw [hv,if_neg (by omega),if_neg (by omega)]
    rfl
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → CurrentAFT.BinaryRootMetadataSerializer.classify_numbering
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → _p2mNS39


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer.role_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged) :
    (role (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) ((inputOrdering choice tagged).symm group)).value=
      RationalPackedRootProgram.nativeRole (RationalFullResponseProgram.selection security r s choice) tagged group := by
  rcases group with (primary | ordinary) | retained
  · apply _p2mNS73
    rw [_p2mNS55]
    exact primary.isLt
  · apply _p2mNS72
    · rw [_p2mNS54]
      omega
    · rw [_p2mNS54]
      have := ordinary.isLt
      omega
  · rw [_p2mNS71 (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inr retained)) (by rw [_p2mNS53];omega),_p2mNS68]
    exact _p2mNS39 security retained.val.val
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → CurrentAFT.BinaryRootMetadataSerializer.role_input
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → _p2mNS70


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer.current_role_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (group : Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged))) :
    (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.roles.get group=
      RationalPackedRootProgram.nativeRole (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged group) := by
  rw [_p2mNS48]
  simpa only [retainedInput, Equiv.symm_apply_apply] using _p2mNS70 choice tagged (inputOrdering choice tagged group)
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → CurrentAFT.BinaryRootMetadataSerializer.current_role_actual
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → _p2mNS49


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security)
    (index : Fin ((groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged))*2)) :
    (matchesBlock (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) (numbering security block) index).value=
      CurrentRootSlotIndex.test (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) block index := by
  rw [_p2mNS59]
  have hc := _p2mNS35 choice tagged ((inputOrdering choice tagged) (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2
  simp only [Equiv.symm_apply_apply] at hc
  have hmap := congrArg (fun value : Option ℕ => value.any (fun number => decide (number=(numbering security block).val))) hc
  apply hmap.trans
  unfold CurrentRootSlotIndex.test CurrentRootSlotIndex.decode
  cases hr : CurrentRootSlotIndex.within (RationalFullResponseProgram.selection security r s choice) tagged
      ((inputOrdering choice tagged) (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2 with
  | none => rfl
  | some root =>
    simp only [Option.map_some,Option.any_some]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he
      exact (numbering security).injective (Fin.ext he)
    · intro he
      rw [he]
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_input
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → _p2mNS58


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer.position_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    (position (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) (numbering security block)).value=
      CurrentRootSlotIndex.position (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) block := by
  change (find _ _).value=_
  rw [_p2mNS52]
  unfold CurrentRootSlotIndex.position
  congr 1
  funext index
  exact _p2mNS58 choice tagged block index
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → CurrentAFT.BinaryRootMetadataSerializer.position_input
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → _p2mNS66


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer.tagSlot_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (tagSlot (primaryInput choice) (ordinaryInput choice) (tagsInput tagged) index).value=
      CurrentRootSlotIndex.taggedSlots (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) index := by
  simp only [tagSlot,readVector_value,_p2mNS77]
  have hp := _p2mNS66 choice tagged (CurrentRootOrdering.tagOrdering tagged index).val
  unfold retainedInput at hp
  rw [hp,CurrentRootSlotIndex.position_tag,_p2mNS74]
  simp only [Option.getD_some,CurrentRootSlotIndex.encode]
  have hinverse (pair : Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) × Fin 2) :
      finProdFinEquiv.symm (finProdFinEquiv pair)=pair := Equiv.symm_apply_apply finProdFinEquiv pair
  exact (hinverse ((inputOrdering choice tagged).symm
      (PairedRootPlacement.tagEmbedding (RationalFullResponseProgram.selection security r s choice) tagged (CurrentRootOrdering.tagOrdering tagged index)).fst,
    CurrentRootSlotIndex.slotNumber (RationalFullResponseProgram.selection security r s choice) tagged
      (PairedRootPlacement.tagEmbedding (RationalFullResponseProgram.selection security r s choice) tagged (CurrentRootOrdering.tagOrdering tagged index)))).trans
    (_p2mNS115 (RationalFullResponseProgram.selection security r s choice) tagged
      (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged index)).symm
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → CurrentAFT.BinaryRootMetadataSerializer.tagSlot_input
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → _p2mNS76


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get index=
      CurrentRootSlotIndex.taggedSlots (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) index := by
  rw [_p2mNS50]
  exact _p2mNS76 choice tagged index
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot_actual
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → _p2mNS51


end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → CurrentAFT.BinaryRootMetadataSerializer.candidate_input
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → _p2mNS35
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → CurrentAFT.BinaryRootMetadataSerializer.classify_numbering
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → _p2mNS39
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → CurrentAFT.BinaryRootMetadataSerializer.current_role_actual
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → _p2mNS49
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot_actual
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → _p2mNS51
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_kept
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → _p2mNS53
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_ordinary
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → _p2mNS54
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_primary
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → _p2mNS55
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_input
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → _p2mNS58
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → CurrentAFT.BinaryRootMetadataSerializer.position_input
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → _p2mNS66
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_at_group
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → _p2mNS68
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → CurrentAFT.BinaryRootMetadataSerializer.role_input
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → _p2mNS70
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → CurrentAFT.BinaryRootMetadataSerializer.tagSlot_input
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → _p2mNS76


end
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → CurrentAFT.BinaryRootMetadataSerializer.classify_numbering
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → _p2mNS39
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → CurrentAFT.BinaryRootMetadataSerializer.position_input
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → _p2mNS66
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → CurrentAFT.BinaryRootMetadataSerializer.role_input
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → _p2mNS70
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_at_group
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → _p2mNS68
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_primary
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → _p2mNS55
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → CurrentAFT.BinaryRootMetadataSerializer.current_role_actual
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → _p2mNS49
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_ordinary
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → _p2mNS54
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_kept
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → _p2mNS53
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot_actual
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → _p2mNS51
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → CurrentAFT.BinaryRootMetadataSerializer.tagSlot_input
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → _p2mNS76
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_input
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → _p2mNS58
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → CurrentAFT.BinaryRootMetadataSerializer.candidate_input
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → _p2mNS35


-- Source module: CurrentAFT.CountedBoundedRootTags
section





/-! # Stored, strictly ordered bounded root tags, with no powerset enumeration -/
namespace CurrentAFT.CountedBoundedRootTags
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false






set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag.nodup {population order : ℕ} (tag : Tag population order) : tag.values.Nodup :=
  tag.increasing.imp (fun h => ne_of_lt h)
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → CurrentAFT.CountedBoundedRootTags.Tag.nodup
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → _p2mNS100

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag.card {population order : ℕ} (tag : Tag population order) : tag.set.card=tag.values.length :=
  List.toFinset_card_of_nodup tag.nodup
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → CurrentAFT.CountedBoundedRootTags.Tag.card
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → _p2mNS99

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag.vector_increasing {population order : ℕ} (tag : Tag population order) : StrictMono tag.vector.get := by
  intro first second hlt
  simpa only [Tag.vector,Vector.get_ofFn] using List.pairwise_iff_get.mp tag.increasing first second hlt
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → CurrentAFT.CountedBoundedRootTags.Tag.vector_increasing
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → _p2mNS103




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag.read_value {population order : ℕ} (tag : Tag population order) (index : Fin tag.values.length) :
    (tag.read index).value=tag.values.get index := by
  simp only [Tag.read,readList_value,List.getElem?_eq_getElem index.isLt,Option.get_some]
  rfl
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → CurrentAFT.CountedBoundedRootTags.Tag.read_value
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → _p2mNS101




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag.store_value {population order : ℕ} (tag : Tag population order) : tag.store.value=tag.vector := by
  apply Vector.ext
  intro index hi
  change (storeData _ tag.read).value.get ⟨index,hi⟩=tag.vector.get ⟨index,hi⟩
  rw [storeData_get,_p2mNS101,Tag.vector,Vector.get_ofFn]
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → CurrentAFT.CountedBoundedRootTags.Tag.store_value
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → _p2mNS102












set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags.entry_sets (population order : ℕ) (size : Fin (order+1)) :
    (entry population order size).value.map Tag.set=
      (countedSubsequences size.val (List.finRange population)).value.map List.toFinset := by
  simp only [entry,List.map_map,Tag.set,Function.comp_def]
  rw [source_value]
  simpa only [List.map_map,Function.comp_def] using congrArg (fun values : List (List (Fin population)) => values.map List.toFinset)
    (List.attach_map_subtype_val _)
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → CurrentAFT.CountedBoundedRootTags.entry_sets
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → _p2mNS105




set_option maxRecDepth 8192
 theorem _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags.flatMap_attach {Input Output : Type*} (inputs : List Input) (function : Input → List Output) :
    inputs.attach.flatMap (fun input => function input.val)=inputs.flatMap function := by
  have h := congrArg (fun values : List Input => values.flatMap function) (List.attach_map_subtype_val inputs)
  simpa only [List.flatMap_map,Function.comp_def] using h
open _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags renaming flatMap_attach → CurrentAFT.CountedBoundedRootTags.flatMap_attach
open _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags renaming flatMap_attach → _p2mNS137


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags.current_sets (population order : ℕ) :
    (current population order).value.map Tag.set=boundedRootList population order := by
  simp only [current,List.map_flatMap,List.flatMap_map,_p2mNS105,boundedRootList]
  exact _p2mNS137 (List.range (order+1)) (fun size => (countedSubsequences size (List.finRange population)).value.map List.toFinset)
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → CurrentAFT.CountedBoundedRootTags.current_sets
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → _p2mNS104













set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags.guarded_value {population order : ℕ} (kernel : Tag population order → RationalResult) (tag : Tag population order) :
    (guarded kernel tag).data.decode=if 2≤tag.set.card then (kernel tag).data.decode else 0 := by
  have ht : (lessCounter 1 tag.values.length).value=true ↔ 2≤tag.set.card := by
    rw [lessCounter_value,_p2mNS99]; omega
  unfold guarded
  try dsimp only
  split <;> rename_i h
  · rw [if_pos (ht.mp h)]
  · rw [if_neg (fun hc => h (ht.mpr hc)),zero_value]
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → CurrentAFT.CountedBoundedRootTags.guarded_value
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → _p2mNS106
























noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags.sum_value (population order : ℕ) (kernel : Tag population order → RationalResult)
    (value : Finset (Fin population) → ℚ) (hvalue : ∀ tag, (kernel tag).data.decode=value tag.set) :
    (sum population order kernel).data.decode=
      ∑ selected∈(FullResponseEnumeration.boundedSubsets (Fin population) order).filter (fun selected => 2≤ selected.card), value selected := by
  rw [sum,_p2mNS32]
  simp only [_p2mNS106,hvalue]
  have he : ((current population order).value.map (fun tag => if 2≤tag.set.card then value tag.set else 0)).sum=
      (((current population order).value.map Tag.set).map (fun selected => if 2≤ selected.card then value selected else 0)).sum := by
    rw [List.map_map]; rfl
  rw [he]
  rw [_p2mNS104,← List.sum_toFinset _ (_p2mNS14 population order)]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext selected
    simp only [Finset.mem_filter,List.mem_toFinset,_p2mNS25,_p2mNS125]
  · intro selected _; rfl
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → CurrentAFT.CountedBoundedRootTags.sum_value
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → _p2mNS107


set_option maxRecDepth 8192
 theorem _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags.bounded_sum {Index : Type*} [Fintype Index] [DecidableEq Index] (order : ℕ) (value : Finset Index → ℚ) :
    (∑ selected∈(FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤ selected.card),value selected)=
      ∑ selected : Finset Index, if 2≤ selected.card ∧ selected.card≤order then value selected else 0 := by
  have hsets : (FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤ selected.card)=
      (Finset.univ : Finset (Finset Index)).filter (fun selected => 2≤ selected.card ∧ selected.card≤order) := by
    ext selected
    simp only [Finset.mem_filter,_p2mNS125,Finset.mem_univ,true_and,and_comm]
  rw [hsets,Finset.sum_filter]
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → CurrentAFT.CountedBoundedRootTags.bounded_sum
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → _p2mNS136


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags.sum_value_equiv {Index : Type*} [Fintype Index] [DecidableEq Index] (population order : ℕ)
    (equiv : Fin population ≃ Index) (kernel : Tag population order → RationalResult) (value : Finset Index → ℚ)
    (hvalue : ∀ tag, (kernel tag).data.decode=value (equiv.finsetCongr tag.set)) :
    (sum population order kernel).data.decode=
      ∑ selected∈(FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤ selected.card), value selected := by
  rw [_p2mNS107 population order kernel (fun selected => value (equiv.finsetCongr selected)) hvalue,_p2mNS136,_p2mNS136]
  have he := equiv.finsetCongr.sum_comp (fun selected => if 2≤ selected.card ∧ selected.card≤order then value selected else 0)
  simpa only [Equiv.finsetCongr_apply,Finset.card_map] using he
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → CurrentAFT.CountedBoundedRootTags.sum_value_equiv
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → _p2mNS108


end
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → CurrentAFT.CountedBoundedRootTags.sum_value
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → _p2mNS107
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → CurrentAFT.CountedBoundedRootTags.sum_value_equiv
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → _p2mNS108
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → CurrentAFT.CountedBoundedRootTags.bounded_sum
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → _p2mNS136

end CurrentAFT.CountedBoundedRootTags
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → CurrentAFT.CountedBoundedRootTags.Tag.card
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → _p2mNS99
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → CurrentAFT.CountedBoundedRootTags.Tag.nodup
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → _p2mNS100
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → CurrentAFT.CountedBoundedRootTags.Tag.read_value
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → _p2mNS101
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → CurrentAFT.CountedBoundedRootTags.Tag.store_value
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → _p2mNS102
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → CurrentAFT.CountedBoundedRootTags.Tag.vector_increasing
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → _p2mNS103
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → CurrentAFT.CountedBoundedRootTags.current_sets
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → _p2mNS104
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → CurrentAFT.CountedBoundedRootTags.entry_sets
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → _p2mNS105
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → CurrentAFT.CountedBoundedRootTags.guarded_value
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → _p2mNS106
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → CurrentAFT.CountedBoundedRootTags.sum_value
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → _p2mNS107
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → CurrentAFT.CountedBoundedRootTags.sum_value_equiv
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → _p2mNS108
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → CurrentAFT.CountedBoundedRootTags.bounded_sum
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → _p2mNS136
open _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags renaming flatMap_attach → CurrentAFT.CountedBoundedRootTags.flatMap_attach
open _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags renaming flatMap_attach → _p2mNS137


end
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → CurrentAFT.CountedBoundedRootTags.Tag.vector_increasing
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → _p2mNS103
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → CurrentAFT.CountedBoundedRootTags.Tag.card
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → _p2mNS99
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → CurrentAFT.CountedBoundedRootTags.sum_value_equiv
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → _p2mNS108
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → CurrentAFT.CountedBoundedRootTags.Tag.nodup
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → _p2mNS100
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → CurrentAFT.CountedBoundedRootTags.sum_value
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → _p2mNS107
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → CurrentAFT.CountedBoundedRootTags.Tag.store_value
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → _p2mNS102
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → CurrentAFT.CountedBoundedRootTags.entry_sets
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → _p2mNS105
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → CurrentAFT.CountedBoundedRootTags.current_sets
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → _p2mNS104
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → CurrentAFT.CountedBoundedRootTags.guarded_value
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → _p2mNS106
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → CurrentAFT.CountedBoundedRootTags.Tag.read_value
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → _p2mNS101


-- Source module: CurrentAFT.BinaryRootMetadataInput
section




/-! Runtime count and input casts for root metadata are proof transports.
All index values, and hence all executed comparisons, are preserved. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize









set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer.tagBlocks_card {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    (tagBlocks tag).card=tag.values.length := by
  rw [tagBlocks,Finset.card_map,_p2mNS99]
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → CurrentAFT.BinaryRootMetadataSerializer.tagBlocks_card
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → _p2mNS75




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer.actualChoice_primary {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) :
    primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1)=primaryInput (actualChoice primary body hp hb) := by
  apply Vector.ext
  intro index hi
  change (primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1)).get ⟨index,hi⟩=
    (primaryInput (actualChoice primary body hp hb)).get ⟨index,hi⟩
  simp only [Vector.get_map,primaryInput,Vector.get_ofFn]
  rfl
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_primary
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → _p2mNS34


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer.actualChoice_ordinary {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) :
    body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1)=ordinaryInput (actualChoice primary body hp hb) := by
  apply Vector.ext
  intro index hi
  change (body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1)).get ⟨index,hi⟩=
    (ordinaryInput (actualChoice primary body hp hb)).get ⟨index,hi⟩
  simp only [Vector.get_map,ordinaryInput,Vector.get_ofFn]
  rfl
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_ordinary
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → _p2mNS33




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer.vector_count_cast_get {first second count : ℕ} (h : first=second) (values : Vector (Fin second) count)
    (index : Fin count) :
    (Eq.mpr (congrArg (fun bound => Vector (Fin bound) count) h) values).get index=Fin.cast h.symm (values.get index) := by
  cases h
  rfl
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_count_cast_get
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → _p2mNS78


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_get {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    (nativeTag tag).get index=Fin.cast (BinaryFullResponseCounts.body_decomposition security).symm (tag.vector.get index) := by
  have h := _p2mNS78 (BinaryFullResponseCounts.body_decomposition security) tag.store.value index
  simpa only [nativeTag,_p2mNS102] using h
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_get
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → _p2mNS60


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_value {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    ((countEquiv security) ((nativeTag tag).get index)).val=(tag.vector.get index).val := by
  rw [_p2mNS60]
  rfl
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_value
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → _p2mNS65


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer.current_congr_counts {legs ordinary queues legs' ordinary' queues' r s tags : ℕ}
    (hl : legs=legs') (ho : ordinary=ordinary') (hq : queues=queues')
    (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    current (legs:=legs') (ordinary:=ordinary') (queues:=queues') (primary.map (Fin.cast hl)) (body.map (Fin.cast ho))
      (tagged.map (Fin.cast (by cases hl;cases ho;cases hq;rfl)))=current primary body tagged := by
  subst legs'
  subst ordinary'
  subst queues'
  simp only [Fin.cast_refl,Vector.map_id_fun,id_eq]
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → CurrentAFT.BinaryRootMetadataSerializer.current_congr_counts
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → _p2mNS42


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer.current_native_counts {security r s order : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    current (primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1))
      (body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1))
      ((nativeTag tag).map (countEquiv security))=current primary body (nativeTag tag) := by
  have he : (countEquiv security : _ → _)=Fin.cast (population_counts security) := by
    funext value
    apply Fin.ext
    rfl
  rw [he]
  exact _p2mNS42 (BinaryFullResponseCounts.current_value security).1
    (BinaryFullResponseCounts.current_value security).2.1 (BinaryFullResponseCounts.current_value security).2.2.1 primary body (nativeTag tag)
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → CurrentAFT.BinaryRootMetadataSerializer.current_native_counts
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → _p2mNS45


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer.vector_mem_toList {α : Type*} {count : ℕ} (values : Vector α count) (value : α) :
    value∈values.toList ↔ ∃ index,values.get index=value := by
  simp only [Vector.mem_toList_iff,Vector.mem_iff_getElem]
  constructor
  · rintro ⟨index,hi,he⟩
    exact ⟨⟨index,hi⟩,he⟩
  · rintro ⟨index,he⟩
    exact ⟨index.val,index.isLt,he⟩
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → CurrentAFT.BinaryRootMetadataSerializer.vector_mem_toList
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → _p2mNS80


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_membership {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order)
    (value : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    value∈((nativeTag tag).map (countEquiv security)).toList ↔ (numbering security).symm value∈tagBlocks tag := by
  rw [_p2mNS80]
  simp only [Vector.get_map,tagBlocks,Finset.mem_map,CountedBoundedRootTags.Tag.set,List.mem_toFinset]
  constructor
  · rintro ⟨index,he⟩
    refine ⟨tag.vector.get index,?_,?_⟩
    · simp only [CountedBoundedRootTags.Tag.vector,Vector.get_ofFn]
      exact List.get_mem _ _
    · rw [← he,_p2mNS60]
      rfl
  · rintro ⟨number,hnumber,he⟩
    obtain ⟨index,hi⟩ := List.mem_iff_get.mp hnumber
    refine ⟨index,?_⟩
    have hv : tag.vector.get index=number := by simpa only [CountedBoundedRootTags.Tag.vector,Vector.get_ofFn] using hi
    apply (numbering security).symm.injective
    rw [_p2mNS60,hv]
    exact he
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_membership
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → _p2mNS62


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_increasing {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    StrictMono (((nativeTag tag).map (countEquiv security)).get) := by
  intro first second hlt
  simp only [Vector.get_map]
  change ((countEquiv security) ((nativeTag tag).get first)).val<((countEquiv security) ((nativeTag tag).get second)).val
  rw [_p2mNS65,_p2mNS65]
  exact tag.vector_increasing hlt
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_increasing
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → _p2mNS61


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    ((nativeTag tag).map (countEquiv security)).get index=
      (tagsInput (tagBlocks tag)).get (Fin.cast (_p2mNS75 tag).symm index) := by
  let values := ((nativeTag tag).map (countEquiv security))
  let target : Fin tag.values.length → Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
    fun index => (tagsInput (tagBlocks tag)).get (Fin.cast (_p2mNS75 tag).symm index)
  have hm : StrictMono values.get := _p2mNS61 tag
  have ht : StrictMono target := by
    intro first second hlt
    exact tagsInput_increasing (tagBlocks tag) hlt
  have he : Set.range values.get=Set.range target := by
    ext value
    constructor
    · rintro ⟨position,hp⟩
      have hm : value∈values.toList := (_p2mNS80 values value).mpr ⟨position,hp⟩
      have hb := (_p2mNS62 tag value).mp hm
      have hn := (tagsInput_range (tagBlocks tag) value).mpr hb
      obtain ⟨position,hp⟩ := (_p2mNS80 _ value).mp hn
      exact ⟨Fin.cast (_p2mNS75 tag) position,hp⟩
    · rintro ⟨position,hp⟩
      have hm : value∈(tagsInput (tagBlocks tag)).toList :=
        (_p2mNS80 _ value).mpr ⟨Fin.cast (_p2mNS75 tag).symm position,hp⟩
      have hb := (tagsInput_range (tagBlocks tag) value).mp hm
      exact (_p2mNS80 values value).mp ((_p2mNS62 tag value).mpr hb)
  exact congrFun ((hm.range_inj ht).mp he) index
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → _p2mNS63


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer.vector_length_cast_get {α : Type*} {first second : ℕ} (h : first=second) (values : Vector α first)
    (index : Fin second) : (values.cast h).get index=values.get (Fin.cast h.symm index) := by
  cases h
  rfl
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_length_cast_get
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → _p2mNS79


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput_vector {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    (nativeTag tag).map (countEquiv security)=(tagsInput (tagBlocks tag)).cast (_p2mNS75 tag) := by
  apply Vector.ext
  intro index hi
  change ((nativeTag tag).map (countEquiv security)).get ⟨index,hi⟩=
    ((tagsInput (tagBlocks tag)).cast (_p2mNS75 tag)).get ⟨index,hi⟩
  rw [_p2mNS79]
  exact _p2mNS63 tag _
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput_vector
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → _p2mNS64




set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer.current_cast_tags {legs ordinary queues r s first second : ℕ} (h : first=second)
    (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) first) :
    current primary body (tagged.cast h)=Result.castTags h (current primary body tagged) := by
  cases h
  simp only [Vector.cast_rfl,Result.castTags]
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.current_cast_tags
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → _p2mNS41


set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer.rational_current_cast_tags {security bits order r s first second : ℕ} (h : first=second)
    (value : Result r s first) (queue : ℤ) (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue (Result.castTags h value).data.metadata sourcePrimary sourceBody=
      RationalPackedRootProgram.current security bits order queue value.data.metadata sourcePrimary sourceBody := by
  cases h
  rfl
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.rational_current_cast_tags
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → _p2mNS67


end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_ordinary
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → _p2mNS33
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_primary
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → _p2mNS34
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.current_cast_tags
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → _p2mNS41
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → CurrentAFT.BinaryRootMetadataSerializer.current_congr_counts
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → _p2mNS42
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → CurrentAFT.BinaryRootMetadataSerializer.current_native_counts
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → _p2mNS45
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_get
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → _p2mNS60
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_increasing
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → _p2mNS61
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_membership
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → _p2mNS62
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → _p2mNS63
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput_vector
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → _p2mNS64
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_value
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → _p2mNS65
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.rational_current_cast_tags
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → _p2mNS67
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → CurrentAFT.BinaryRootMetadataSerializer.tagBlocks_card
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → _p2mNS75
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_count_cast_get
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → _p2mNS78
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_length_cast_get
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → _p2mNS79
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → CurrentAFT.BinaryRootMetadataSerializer.vector_mem_toList
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → _p2mNS80


end
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput_vector
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → _p2mNS64
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_value
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → _p2mNS65
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_count_cast_get
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → _p2mNS78
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.current_cast_tags
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → _p2mNS41
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → CurrentAFT.BinaryRootMetadataSerializer.current_congr_counts
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → _p2mNS42
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_increasing
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → _p2mNS61
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → CurrentAFT.BinaryRootMetadataSerializer.current_native_counts
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → _p2mNS45
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_membership
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → _p2mNS62
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → CurrentAFT.BinaryRootMetadataSerializer.vector_mem_toList
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → _p2mNS80
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_primary
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → _p2mNS34
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.rational_current_cast_tags
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → _p2mNS67
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → _p2mNS63
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_get
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → _p2mNS60
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_ordinary
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → _p2mNS33
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → CurrentAFT.BinaryRootMetadataSerializer.tagBlocks_card
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → _p2mNS75
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_length_cast_get
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → _p2mNS79


-- Source module: CurrentAFT.BinaryRootMetadataTransport
section


/-! Proof-only cardinal transport identifies the produced finite metadata
with the paper's actual arrays, before any polynomial physical image. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open RationalRootGroupProgram
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize




 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer.current_castMetadata {r s kept kept' tags : ℕ} (security bits order : ℕ) (queue : ℤ)
    (h : kept=kept') (data : RationalPackedRootProgram.Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue data sourcePrimary sourceBody=
      RationalPackedRootProgram.current security bits order queue (castMetadata h data) sourcePrimary sourceBody := by
  subst kept'
  rfl
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → CurrentAFT.BinaryRootMetadataSerializer.current_castMetadata
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → _p2mNS40


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer.current_metadata_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    castMetadata (retainedInput_length choice tagged)
      (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.metadata =
      RationalPackedRootProgram.actualMetadata (RationalFullResponseProgram.selection security r s choice) tagged := by
  apply congrArg₂ RationalPackedRootProgram.Metadata.mk
  · funext group
    change (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.roles.get
      ((groupCast choice tagged).symm group)=_
    rw [_p2mNS49]
    change RationalPackedRootProgram.nativeRole _ _
      ((RationalPackedRootProgram.ordering _ _) ((groupCast choice tagged) ((groupCast choice tagged).symm group)))=_
    rw [Equiv.apply_symm_apply]
  · funext tag
    change ((groupCast choice tagged) ((current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get tag).1,
      ((current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get tag).2)=_
    simp only [_p2mNS51]
    change ((groupCast choice tagged) (CurrentRootSlotIndex.tagPosition _ _ (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged tag)).1,
      (CurrentRootSlotIndex.tagPosition _ _ (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged tag)).2)=
        CurrentRootSlotIndex.tagPosition _ _ (RationalPackedRootProgram.ordering _ _) (CurrentRootOrdering.tagOrdering tagged tag)
    simp only [_p2mNS115]
    apply Prod.ext
    · change (groupCast choice tagged) ((inputOrdering choice tagged).symm _)=_
      simp only [inputOrdering,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
    · rfl
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → CurrentAFT.BinaryRootMetadataSerializer.current_metadata_actual
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → _p2mNS44


 set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer.current_rational_actual {security r s : ℕ} (bits order : ℕ) (queue : ℤ)
    (choice : UniformTaggedOutput.Choice security r s) (tagged : Finset (BlockIndex security))
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue
      (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.metadata sourcePrimary sourceBody =
      RationalPackedRootProgram.current security bits order queue
        (RationalPackedRootProgram.actualMetadata (RationalFullResponseProgram.selection security r s choice) tagged) sourcePrimary sourceBody := by
  rw [_p2mNS40 security bits order queue (retainedInput_length choice tagged),_p2mNS44]
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → CurrentAFT.BinaryRootMetadataSerializer.current_rational_actual
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → _p2mNS46


end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → CurrentAFT.BinaryRootMetadataSerializer.current_castMetadata
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → _p2mNS40
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → CurrentAFT.BinaryRootMetadataSerializer.current_metadata_actual
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → _p2mNS44
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → CurrentAFT.BinaryRootMetadataSerializer.current_rational_actual
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → _p2mNS46


end
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → CurrentAFT.BinaryRootMetadataSerializer.current_metadata_actual
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → _p2mNS44
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → CurrentAFT.BinaryRootMetadataSerializer.current_rational_actual
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → _p2mNS46
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → CurrentAFT.BinaryRootMetadataSerializer.current_castMetadata
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → _p2mNS40


-- Source module: CurrentAFT.BinaryRootMetadataNative
section



/-! The executed native metadata produces the literal actual response table. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize BinaryFullResponseCounts.current

set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer.current_rational_native {security r s tagOrder : ℕ} (bits order : ℕ) (queue : ℤ)
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get)
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body tagOrder)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue
      (current primary body (nativeTag tag)).data.metadata sourcePrimary sourceBody=
    RationalPackedRootProgram.current security bits order queue
      (RationalPackedRootProgram.actualMetadata
        (RationalFullResponseProgram.selection security r s (actualChoice primary body hp hb)) (tagBlocks tag))
      sourcePrimary sourceBody := by
  rw [← _p2mNS45 primary body tag,_p2mNS34 primary body hp hb,
    _p2mNS33 primary body hp hb,_p2mNS64,_p2mNS41,_p2mNS67]
  exact _p2mNS46 bits order queue (actualChoice primary body hp hb) (tagBlocks tag) sourcePrimary sourceBody
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → CurrentAFT.BinaryRootMetadataSerializer.current_rational_native
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → _p2mNS47




end CurrentAFT.BinaryRootMetadataSerializer
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → CurrentAFT.BinaryRootMetadataSerializer.current_rational_native
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → _p2mNS47


end
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → CurrentAFT.BinaryRootMetadataSerializer.current_rational_native
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → _p2mNS47


